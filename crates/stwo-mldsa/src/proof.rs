//! Standalone prove/verify for the `mldsa_coeffs` component + verifier-native
//! fold, wired through the `air-core` orchestrator. Scaffolding mirroring
//! `stwo-p256`'s claim/statement conventions so M7 can register the component.
//!
//! One air-core module (`CoeffsModule`) contributes, in commit order:
//!   1. `coeffs`          — the tall stacked bivariate-Horner component.
//!   2. rc table providers — `rc9`, `rc13`, `rc8`, `rc7` (one each).
//!
//! and folds two non-component terms into its `claimed_sums`:
//!   * the coeffs component's logup residue,
//!   * the verifier-native `EvalAtRs` USE sum (`+Σ 1/combine(poly_id, ê_i)`),
//!     which cancels the component's group-end YIELDs iff the claimed evals equal
//!     the committed accumulator — and the same claimed evals must satisfy the
//!     folded identity `(‡) == 0` (checked structurally, [`verify`]).
//!
//! Transcript order (worksheet §3.2 / GAP-1a): mix public `(ρ, t1)` → commit base
//! (digits + carries + c + norm/rc aux) → draw `ρ_RLC, r, s` + relations → commit
//! interaction. `air-core` enforces this ordering.

use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, Relation, TraceLocationAllocator};

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use crate::air_util::padded_log_size;
use crate::air_util::{m31, ColEval};
use crate::balancer::{
    balancer_base_cols, gen_balancer_interaction, gen_balancer_trace, BalancerEval,
    BalancerRelation, BALANCER_INTERACTION_COLS,
};
use crate::binding::{CCELL_ARITY, WCELL_ARITY};
use crate::coeffs::layout::{active_rows, groups, Kind, N_GROUPS};
use crate::coeffs::relations::CoeffsRelations;
use crate::coeffs::tables::{
    gen_table_interaction, gen_table_multiplicities, gen_table_preprocessed, RcKind, RcTableEval,
    RC_TABLE_INTERACTION_COLS,
};
use crate::coeffs::{
    coeffs_preprocessed_ids, gen_coeffs_base_trace, gen_coeffs_interaction,
    gen_coeffs_preprocessed, gen_coeffs_rc_uses, CoeffsEval, N_BASE_COLS, N_INTERACTION_COLS,
};
use crate::types::MlDsaVerifyInput;
use crate::verifier_native::{compute_public_evals, folded_check, ClaimedEvals};
use crate::witness::MlDsaWitness;

/// The public statement + prover claims of a coeffs proof.
#[derive(Clone, Serialize, Deserialize)]
pub struct CoeffsProof {
    pub input: MlDsaVerifyInput,
    /// The 30 claimed `P̂(r,s)` group evaluations, in poly_id order.
    pub group_evals: Vec<SecureField>,
    pub coeffs_claimed_sum: SecureField,
    pub rc_claimed_sums: [SecureField; 5],
    pub wcell_claimed_sum: SecureField,
    pub ccell_claimed_sum: SecureField,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

fn coeffs_log_size() -> u32 {
    padded_log_size(active_rows())
}

/// The `coeffs` component's `TreeLayout` contribution.
fn coeffs_trace_layout() -> Vec<u32> {
    vec![coeffs_log_size(); N_BASE_COLS]
}
fn coeffs_interaction_layout() -> Vec<u32> {
    vec![coeffs_log_size(); N_INTERACTION_COLS]
}

fn all_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = coeffs_preprocessed_ids();
    for kind in RcKind::ALL {
        ids.push(kind.value_column_id());
    }
    ids
}

fn all_preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = vec![coeffs_log_size(); coeffs_preprocessed_ids().len()];
    for kind in RcKind::ALL {
        sizes.push(kind.log_size());
    }
    sizes
}

fn gen_all_preprocessed() -> Vec<ColEval> {
    let mut cols = gen_coeffs_preprocessed(coeffs_log_size());
    for kind in RcKind::ALL {
        cols.push(gen_table_preprocessed(kind));
    }
    cols
}

fn mix_public(channel: &mut Blake2sChannel, input: &MlDsaVerifyInput) {
    for b in &input.rho {
        channel.mix_u64(*b as u64);
    }
    for i in 0..crate::constants::K {
        for m in 0..crate::constants::N {
            channel.mix_u64(input.t1[i][m] as u64);
        }
    }
    // NOTE: the claimed `group_evals` are NOT mixed here — the prover does not
    // know them until after the base commit + challenge draw (they depend on
    // r,s). They are mixed with the claimed sums instead (`mix_claimed_sums`),
    // which air-core folds in just before the interaction-tree commit. Mixing
    // them in `mix_public` would diverge the prover transcript (group_evals still
    // zero at that point) from the verifier's.
}

/// Centered M31 encoding of a signed value (matches `coeffs::encode_signed`).
fn enc(v: i128) -> u32 {
    const P: i128 = (1 << 31) - 1;
    (((v % P) + P) % P) as u32
}

/// The `(w_bind_id, w)` tuples the coeffs W groups YIELD (one per w-coefficient),
/// which the standalone test's WCell balancer CONSUMES (+). In the composed
/// statement decomp is the consumer instead.
fn wcell_tuples(witness: &MlDsaWitness) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    for g in groups() {
        if g.kind == Kind::W {
            let i = (g.poly_id - crate::coeffs::layout::POLY_ID_W0) as usize;
            for m in 0..g.coeffs {
                out.push(vec![
                    (i * crate::constants::N + m) as u32,
                    witness.rows[i].w[m],
                ]);
            }
        }
    }
    out
}

/// The `(c_bind_id, c)` tuples the coeffs C group YIELDs, consumed by the
/// standalone test's CCell balancer (composed: sampleinball consumes).
fn ccell_tuples(witness: &MlDsaWitness) -> Vec<Vec<u32>> {
    (0..crate::constants::N)
        .map(|m| vec![m as u32, enc(witness.digits.c[m])])
        .collect()
}

fn wcell_log_size() -> u32 {
    padded_log_size(crate::constants::K * crate::constants::N)
}
fn ccell_log_size() -> u32 {
    padded_log_size(crate::constants::N)
}

// =============================================================================
// Prover / verifier holders.
// =============================================================================

struct Built {
    coeffs: FrameworkComponent<CoeffsEval>,
    rc: Vec<FrameworkComponent<RcTableEval>>,
    wcell: FrameworkComponent<BalancerEval>,
    ccell: FrameworkComponent<BalancerEval>,
}

impl Built {
    fn as_components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.coeffs];
        out.extend(self.rc.iter().map(|c| c as &dyn Component));
        out.push(&self.wcell);
        out.push(&self.ccell);
        out
    }
    fn as_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = vec![&self.coeffs];
        out.extend(
            self.rc
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.push(&self.wcell);
        out.push(&self.ccell);
        out
    }
}

pub struct CoeffsProver {
    witness: MlDsaWitness,
    input: MlDsaVerifyInput,
    // filled during proving:
    r: SecureField,
    s: SecureField,
    rho_rlc: SecureField,
    relations: Option<CoeffsRelations>,
    group_evals: Vec<SecureField>,
    coeffs_claimed_sum: SecureField,
    rc_claimed_sums: [SecureField; 5],
    wcell_claimed_sum: SecureField,
    ccell_claimed_sum: SecureField,
    native_use_sum: SecureField,
    rc_mult: Vec<ColEval>,
    built: Option<Built>,
}

struct CoeffsVerifier {
    input: MlDsaVerifyInput,
    group_evals: Vec<SecureField>,
    coeffs_claimed_sum: SecureField,
    rc_claimed_sums: [SecureField; 5],
    wcell_claimed_sum: SecureField,
    ccell_claimed_sum: SecureField,
    r: SecureField,
    s: SecureField,
    rho_rlc: SecureField,
    relations: Option<CoeffsRelations>,
    native_use_sum: SecureField,
    fold_ok: bool,
    built: Option<Built>,
}

/// Draw `ρ_RLC, r, s` then the relations, in the fixed order both sides use.
fn draw_challenges(
    channel: &mut Blake2sChannel,
) -> (SecureField, SecureField, SecureField, CoeffsRelations) {
    let rho_rlc = channel.draw_secure_felt();
    let r = channel.draw_secure_felt();
    let s = channel.draw_secure_felt();
    let relations = CoeffsRelations::draw(channel);
    (rho_rlc, r, s, relations)
}

/// The verifier-native EvalAtRs USE sum: `+Σ_id 1/combine(poly_id, coords)`.
fn native_use_sum(group_evals: &[SecureField], relations: &CoeffsRelations) -> SecureField {
    let one = SecureField::from(m31(1));
    let mut sum = SecureField::zero();
    for (poly_id, eval) in group_evals.iter().enumerate() {
        let coords = eval.to_m31_array();
        let tuple = [
            m31(poly_id as u32),
            coords[0],
            coords[1],
            coords[2],
            coords[3],
        ];
        let denom: SecureField = relations.eval.combine(&tuple);
        sum += one / denom;
    }
    sum
}

#[allow(clippy::too_many_arguments)]
fn build_components(
    allocator: &mut TraceLocationAllocator,
    log_size: u32,
    r: SecureField,
    s: SecureField,
    relations: &CoeffsRelations,
    coeffs_claimed_sum: SecureField,
    rc_claimed_sums: &[SecureField; 5],
    wcell_claimed_sum: SecureField,
    ccell_claimed_sum: SecureField,
) -> Built {
    let coeffs = FrameworkComponent::new(
        allocator,
        CoeffsEval {
            log_size,
            r,
            s,
            relations: relations.clone(),
        },
        coeffs_claimed_sum,
    );
    let mut rc = Vec::with_capacity(4);
    for (idx, kind) in RcKind::ALL.iter().enumerate() {
        rc.push(FrameworkComponent::new(
            allocator,
            RcTableEval {
                kind: *kind,
                relation: relations.rc(*kind).clone(),
            },
            rc_claimed_sums[idx],
        ));
    }
    // Test-side consumers of the WCell / CCell yields (coeffs yields −, balancer
    // consumes +). In the composed statement decomp / sampleinball replace these.
    let wcell = FrameworkComponent::new(
        allocator,
        BalancerEval {
            log_size: wcell_log_size(),
            arity: WCELL_ARITY,
            relation: BalancerRelation::WCell(relations.wcell.clone()),
            sign_positive: true,
        },
        wcell_claimed_sum,
    );
    let ccell = FrameworkComponent::new(
        allocator,
        BalancerEval {
            log_size: ccell_log_size(),
            arity: CCELL_ARITY,
            relation: BalancerRelation::CCell(relations.ccell.clone()),
            sign_positive: true,
        },
        ccell_claimed_sum,
    );
    Built {
        coeffs,
        rc,
        wcell,
        ccell,
    }
}

impl Air for CoeffsProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(channel, &self.input);
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let (rho_rlc, r, s, relations) = draw_challenges(channel);
        self.rho_rlc = rho_rlc;
        self.r = r;
        self.s = s;
        self.relations = Some(relations);
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: all_preprocessed_log_sizes(),
            trace: module_trace_layout(),
            interaction: module_interaction_layout(),
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        let mut sums = vec![self.coeffs_claimed_sum];
        sums.extend(self.rc_claimed_sums);
        sums.push(self.wcell_claimed_sum);
        sums.push(self.ccell_claimed_sum);
        sums.push(self.native_use_sum);
        sums
    }
    fn mix_claimed_sums(&self, channel: &mut Blake2sChannel) {
        // The claimed group evals are bound here (they depend on r,s and are only
        // known post-base-commit). Mixed BEFORE the interaction-tree commit, in
        // the same slot on both sides.
        channel.mix_felts(&self.group_evals);
        channel.mix_felts(&self.claimed_sums());
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            coeffs_log_size(),
            self.r,
            self.s,
            self.relations.as_ref().expect("relations drawn"),
            self.coeffs_claimed_sum,
            &self.rc_claimed_sums,
            self.wcell_claimed_sum,
            self.ccell_claimed_sum,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").as_components()
    }
}

/// Base-trace column log-sizes: coeffs base cols + one rc multiplicity column
/// per table (at the table's own log_size) + the two balancer traces.
fn module_trace_layout() -> Vec<u32> {
    let mut trace = coeffs_trace_layout();
    for kind in RcKind::ALL {
        trace.push(kind.log_size());
    }
    for _ in 0..balancer_base_cols(WCELL_ARITY) {
        trace.push(wcell_log_size());
    }
    for _ in 0..balancer_base_cols(CCELL_ARITY) {
        trace.push(ccell_log_size());
    }
    trace
}

/// Interaction column log-sizes: coeffs interaction cols + one batched logup
/// column (`RC_TABLE_INTERACTION_COLS` base cols) per table + the two balancers.
fn module_interaction_layout() -> Vec<u32> {
    let mut interaction = coeffs_interaction_layout();
    for kind in RcKind::ALL {
        for _ in 0..RC_TABLE_INTERACTION_COLS {
            interaction.push(kind.log_size());
        }
    }
    for _ in 0..BALANCER_INTERACTION_COLS {
        interaction.push(wcell_log_size());
    }
    for _ in 0..BALANCER_INTERACTION_COLS {
        interaction.push(ccell_log_size());
    }
    interaction
}

impl AirProver for CoeffsProver {
    fn max_log_size(&self) -> u32 {
        coeffs_log_size()
            .max(RcKind::Rc13.log_size())
            .max(wcell_log_size())
            .max(ccell_log_size())
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        coeffs_log_size() + 2
    }
    fn store_polynomial_coefficients(&self) -> bool {
        // A-707: the standalone test profile's blowup is below the batch-4
        // degree excess, so retain coefficients here; production blowup-4 does
        // not need this memory tradeoff.
        true
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_all_preprocessed());
    }
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "mldsa_coeffs",
            &all_preprocessed_ids(),
            &gen_all_preprocessed(),
        )
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut evals = gen_coeffs_base_trace(&self.witness, coeffs_log_size());
        // Multiplicity columns depend only on the witness, not on relations.
        let rc_uses = gen_coeffs_rc_uses(&self.witness);
        self.rc_mult = RcKind::ALL
            .iter()
            .map(|kind| gen_table_multiplicities(*kind, rc_uses.for_kind(*kind)))
            .collect();
        evals.extend(self.rc_mult.clone());
        evals.extend(gen_balancer_trace(
            wcell_log_size(),
            &wcell_tuples(&self.witness),
        ));
        evals.extend(gen_balancer_trace(
            ccell_log_size(),
            &ccell_tuples(&self.witness),
        ));
        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let relations = self.relations.clone().expect("relations drawn");
        let interaction =
            gen_coeffs_interaction(&self.witness, coeffs_log_size(), self.r, self.s, &relations);
        let mut evals = interaction.trace;
        self.coeffs_claimed_sum = interaction.claimed_sum;
        self.group_evals = interaction.group_evals.clone();

        for (idx, kind) in RcKind::ALL.iter().enumerate() {
            let (tr, sum) = gen_table_interaction(*kind, &self.rc_mult[idx], relations.rc(*kind));
            evals.extend(tr);
            self.rc_claimed_sums[idx] = sum;
        }
        let (wtr, wsum) = gen_balancer_interaction(
            wcell_log_size(),
            &wcell_tuples(&self.witness),
            &BalancerRelation::WCell(relations.wcell.clone()),
            true,
        );
        self.wcell_claimed_sum = wsum;
        evals.extend(wtr);
        let (ctr, csum) = gen_balancer_interaction(
            ccell_log_size(),
            &ccell_tuples(&self.witness),
            &BalancerRelation::CCell(relations.ccell.clone()),
            true,
        );
        self.ccell_claimed_sum = csum;
        evals.extend(ctr);
        tb.extend_evals(evals);

        self.native_use_sum = native_use_sum(&self.group_evals, &relations);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built.as_ref().expect("built").as_prover()
    }
}

impl Air for CoeffsVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(channel, &self.input);
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let (rho_rlc, r, s, relations) = draw_challenges(channel);
        self.rho_rlc = rho_rlc;
        self.r = r;
        self.s = s;
        self.native_use_sum = native_use_sum(&self.group_evals, &relations);
        // The folded identity (‡) must hold on the claimed evals.
        let public = compute_public_evals(&self.input, r, s);
        let fold = folded_check(
            &public,
            &ClaimedEvals(&self.group_evals),
            self.rho_rlc,
            r,
            s,
        );
        self.fold_ok = fold == SecureField::zero();
        self.relations = Some(relations);
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: all_preprocessed_log_sizes(),
            trace: module_trace_layout(),
            interaction: module_interaction_layout(),
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        let mut sums = vec![self.coeffs_claimed_sum];
        sums.extend(self.rc_claimed_sums);
        sums.push(self.wcell_claimed_sum);
        sums.push(self.ccell_claimed_sum);
        sums.push(self.native_use_sum);
        sums
    }
    fn mix_claimed_sums(&self, channel: &mut Blake2sChannel) {
        channel.mix_felts(&self.group_evals);
        channel.mix_felts(&self.claimed_sums());
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            coeffs_log_size(),
            self.r,
            self.s,
            self.relations.as_ref().expect("relations drawn"),
            self.coeffs_claimed_sum,
            &self.rc_claimed_sums,
            self.wcell_claimed_sum,
            self.ccell_claimed_sum,
        ));
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        // Reconstruct tree-0 verifier-side so the pinned-root check in
        // `verify_coeffs` has canonical content to compare against. Same columns
        // the prover commits (`gen_all_preprocessed`), in `all_preprocessed_ids`
        // order — mirrors the MlDsaVerifier override in statement.rs.
        Ok(gen_all_preprocessed())
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").as_components()
    }
}

// =============================================================================
// Entry points.
// =============================================================================

pub fn prove_coeffs(
    witness: MlDsaWitness,
    input: MlDsaVerifyInput,
    config: PcsConfig,
) -> Result<CoeffsProof, ProvingError> {
    let mut prover = CoeffsProver {
        witness,
        input: input.clone(),
        r: SecureField::zero(),
        s: SecureField::zero(),
        rho_rlc: SecureField::zero(),
        relations: None,
        group_evals: vec![SecureField::zero(); N_GROUPS],
        coeffs_claimed_sum: SecureField::zero(),
        rc_claimed_sums: [SecureField::zero(); 5],
        wcell_claimed_sum: SecureField::zero(),
        ccell_claimed_sum: SecureField::zero(),
        native_use_sum: SecureField::zero(),
        rc_mult: Vec::new(),
        built: None,
    };
    let stark_proof = air_core::prove(&mut [&mut prover], config)?;
    Ok(CoeffsProof {
        input,
        group_evals: prover.group_evals,
        coeffs_claimed_sum: prover.coeffs_claimed_sum,
        rc_claimed_sums: prover.rc_claimed_sums,
        wcell_claimed_sum: prover.wcell_claimed_sum,
        ccell_claimed_sum: prover.ccell_claimed_sum,
        stark_proof,
    })
}

/// Verify a standalone coeffs proof under the caller's exact PCS policy.
///
/// Standalone callers are responsible for choosing this policy; accepting the
/// proof-carried configuration would let an untrusted proof lower its own
/// verification security parameters.
pub fn verify_coeffs(
    proof: &CoeffsProof,
    expected_config: PcsConfig,
) -> Result<(), VerificationError> {
    if proof.stark_proof.config != expected_config {
        return Err(VerificationError::InvalidStructure(
            "mldsa_coeffs: unexpected PCS configuration".into(),
        ));
    }
    let mut verifier = CoeffsVerifier {
        input: proof.input.clone(),
        group_evals: proof.group_evals.clone(),
        coeffs_claimed_sum: proof.coeffs_claimed_sum,
        rc_claimed_sums: proof.rc_claimed_sums,
        wcell_claimed_sum: proof.wcell_claimed_sum,
        ccell_claimed_sum: proof.ccell_claimed_sum,
        r: SecureField::zero(),
        s: SecureField::zero(),
        rho_rlc: SecureField::zero(),
        relations: None,
        native_use_sum: SecureField::zero(),
        fold_ok: false,
        built: None,
    };
    // The air-core verify redraws challenges (in draw_relations) then checks the
    // global logup balance + the STARK proof. We additionally require the native
    // folded identity to vanish.
    let expected_root =
        air_core::compute_canonical_preprocessed_root(&mut [&mut verifier], expected_config)?;
    air_core::verify_with_expected_preprocessed_root(
        &mut [&mut verifier],
        &proof.stark_proof,
        Some(expected_root),
    )
    .map_err(|error| match error {
        air_core::VerifyError::Stark(error) => error,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => {
            VerificationError::InvalidStructure(
                "mldsa_coeffs: preprocessed root mismatch (forged tree-0)".into(),
            )
        }
    })?;
    if !verifier.fold_ok {
        return Err(VerificationError::InvalidStructure(
            "mldsa_coeffs: folded identity (‡) is nonzero".into(),
        ));
    }
    Ok(())
}

/// Interaction-column arity sanity (mix parity for [`SECURE_EXTENSION_DEGREE`]).
const _: () = assert!(N_INTERACTION_COLS.is_multiple_of(SECURE_EXTENSION_DEGREE));
