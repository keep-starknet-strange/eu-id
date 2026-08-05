//! Test harness for `mldsa_decomp` through the `air-core` orchestrator. The
//! module contributes, in commit order:
//!   1. `decomp`             — the [DECOMP]+[HINT] byte-pair component.
//!   2. `range_table`         — the shared `(value, bound_id)` range table
//!      (C5), self-drawn here (standalone mode) rather than shared through a
//!      hosted handle.
//!   3. `wcell_provider`      — TEST-SIDE balancer: yields the `(w_bind_id, w)`
//!      tuples that decomp consumes. It stands in for the coefficient W-cell
//!      yields in the composed statement.
//!   4. `hashio_consumer`     — TEST-SIDE balancer: consumes the 768 `w1Encode`
//!      bytes that decomp yields. It stands in for the sponge absorb side.
//!
//! Transcript order: mix nothing public (the witness is the statement here) →
//! commit base → draw relations → commit interaction. `air-core` enforces it.

use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::SimdBackend;
#[cfg(test)]
use stwo::prover::backend::Column;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use crate::air_util::{padded_log_size, ColEval};
use crate::binding::STREAM_ID_CTILDE_ABSORB;
use crate::coeffs::tables::{
    gen_range_table_interaction, gen_range_table_multiplicities, gen_range_table_preprocessed,
    range_table_log_size, range_table_preprocessed_ids, RangeTableEval, RANGE_TABLE_INTERACTION_COLS,
};
use crate::coeffs::tables::RcKind;
use crate::profile::ML_DSA_65;
use crate::witness::MlDsaWitness;

#[cfg(not(test))]
use super::gen_decomp_metadata;
use super::relations::DecompRelations;
use super::{
    decomp_preprocessed_ids, gen_decomp_base_trace, gen_decomp_interaction,
    gen_decomp_preprocessed, DecompEval, DecompMetadata, N_BASE_COLS, N_INTERACTION_COLS, N_ROWS,
};
#[cfg(test)]
use super::{
    gen_decomp_interaction_with_test_options, gen_decomp_metadata_with_test_options,
    DecompTracePoke, COL_HINT_ACC, COL_LANE0, COL_V_ZERO, L_A_HI, L_B_HI, L_HINT, L_S0,
    L_SIGN_HI, L_SIGN_VAL, L_W, L_W0, L_W1, L_W1P, L_WRAPK, L_WRAP_M,
};
use crate::balancer::{
    gen_balancer_interaction, gen_balancer_trace, BalancerEval, BalancerRelation,
    BALANCER_INTERACTION_COLS,
};

/// The public statement + prover claims of a decomp proof.
pub struct DecompProof {
    pub decomp_claimed_sum: SecureField,
    pub range_claimed_sum: SecureField,
    pub wcell_claimed_sum: SecureField,
    pub hashio_claimed_sum: SecureField,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

fn decomp_log_size() -> u32 {
    padded_log_size(N_ROWS)
}

fn all_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = decomp_preprocessed_ids(ML_DSA_65);
    ids.extend(range_table_preprocessed_ids());
    ids
}

fn all_preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = vec![decomp_log_size(); decomp_preprocessed_ids(ML_DSA_65).len()];
    sizes.extend(vec![range_table_log_size(); range_table_preprocessed_ids().len()]);
    sizes
}

fn gen_all_preprocessed() -> Vec<ColEval> {
    let mut cols = gen_decomp_preprocessed(ML_DSA_65, decomp_log_size());
    cols.extend(gen_range_table_preprocessed());
    cols
}

/// This standalone harness's own range-use census, converted to the 7-slot
/// shape [`gen_range_table_multiplicities`] expects. Only Rc4/Rc13/Rc7/Rc8
/// are ever nonzero for decomp; the rest stay at the `RcUses::new()` zero
/// default.
fn range_uses_arrays(rc_uses: &crate::coeffs::RcUses) -> [&[u32]; 8] {
    core::array::from_fn(|index| rc_uses.for_kind(RcKind::ALL[index]))
}

// The two balancer components' log sizes (padded to their tuple counts).
fn wcell_log_size() -> u32 {
    padded_log_size(crate::constants::K * crate::constants::N) // 1536
}
fn hashio_log_size() -> u32 {
    padded_log_size(crate::profile::ML_DSA_65.w1_encoded_bytes())
}

struct Built {
    decomp: FrameworkComponent<DecompEval>,
    range: FrameworkComponent<RangeTableEval>,
    wcell: FrameworkComponent<BalancerEval>,
    hashio: FrameworkComponent<BalancerEval>,
}

impl Built {
    fn as_components(&self) -> Vec<&dyn Component> {
        vec![
            &self.decomp as &dyn Component,
            &self.range as &dyn Component,
            &self.wcell as &dyn Component,
            &self.hashio as &dyn Component,
        ]
    }
    fn as_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.decomp as &dyn ComponentProver<SimdBackend>,
            &self.range as &dyn ComponentProver<SimdBackend>,
            &self.wcell as &dyn ComponentProver<SimdBackend>,
            &self.hashio as &dyn ComponentProver<SimdBackend>,
        ]
    }
}

/// Which balancer role: yield the wcell tuples (+ provider) / consume the bytes.
fn wcell_tuples(witness: &MlDsaWitness) -> Vec<Vec<u32>> {
    // (w_bind_id, w) for every w coefficient — the coeffs W-cell yields.
    let mut out = Vec::with_capacity(crate::constants::K * crate::constants::N);
    for i in 0..crate::constants::K {
        for m in 0..crate::constants::N {
            out.push(vec![
                (i * crate::constants::N + m) as u32,
                witness.rows[i].w[m],
            ]);
        }
    }
    out
}

fn hashio_tuples(bytes: &[u8]) -> Vec<Vec<u32>> {
    bytes
        .iter()
        .enumerate()
        .map(|(pos, &b)| vec![STREAM_ID_CTILDE_ABSORB, pos as u32, b as u32])
        .collect()
}

pub struct DecompProver {
    witness: MlDsaWitness,
    #[cfg(test)]
    checked_hint_total: Option<u32>,
    #[cfg(test)]
    trace_poke: Option<DecompTracePoke>,
    relations: Option<DecompRelations>,
    decomp_claimed_sum: SecureField,
    range_claimed_sum: SecureField,
    wcell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    range_mult: Option<ColEval>,
    w1_encode_bytes: Vec<u8>,
    built: Option<Built>,
}

impl DecompProver {
    #[cfg(test)]
    fn gen_interaction(&self, relations: &DecompRelations) -> super::DecompInteraction {
        gen_decomp_interaction_with_test_options(
            &self.witness,
            decomp_log_size(),
            STREAM_ID_CTILDE_ABSORB,
            relations,
            self.checked_hint_total,
            self.trace_poke,
        )
    }

    #[cfg(not(test))]
    fn gen_interaction(&self, relations: &DecompRelations) -> super::DecompInteraction {
        gen_decomp_interaction(
            &self.witness,
            decomp_log_size(),
            STREAM_ID_CTILDE_ABSORB,
            relations,
        )
    }

    #[cfg(test)]
    fn gen_metadata(&self) -> DecompMetadata {
        gen_decomp_metadata_with_test_options(
            &self.witness,
            self.checked_hint_total,
            self.trace_poke,
        )
    }

    #[cfg(not(test))]
    fn gen_metadata(&self) -> DecompMetadata {
        gen_decomp_metadata(&self.witness)
    }
}

#[cfg(test)]
fn apply_trace_poke(evals: &mut [ColEval], poke: DecompTracePoke) {
    let row = crate::air_util::circle_row_to_coset(decomp_log_size())
        .iter()
        .position(|&coset| coset == 0)
        .expect("first decomp row");
    let mut set_lane0 = |offset: usize, value: i64| {
        evals[COL_LANE0 + offset]
            .values
            .set(row, crate::air_util::enc_signed(value));
    };
    let lane = poke.lane();
    set_lane0(L_W, lane.w);
    set_lane0(L_W1, lane.w1);
    set_lane0(L_W0, lane.w0);
    set_lane0(L_HINT, lane.hint);
    set_lane0(L_WRAPK, lane.wrap_k);
    set_lane0(L_S0, lane.s0);
    set_lane0(L_W1P, lane.w1p);
    set_lane0(L_WRAP_M, lane.wrap_m);
    set_lane0(L_A_HI, lane.a_hi);
    set_lane0(L_B_HI, lane.b_hi);
    set_lane0(L_SIGN_VAL, lane.sign_val);
    set_lane0(L_SIGN_HI, lane.sign_hi);
    evals[COL_V_ZERO[0]]
        .values
        .set(row, crate::air_util::m31(lane.v_is_zero as u32));
}

struct DecompVerifier {
    decomp_claimed_sum: SecureField,
    range_claimed_sum: SecureField,
    wcell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    relations: Option<DecompRelations>,
    built: Option<Built>,
}

fn build_components(
    allocator: &mut TraceLocationAllocator,
    relations: &DecompRelations,
    decomp_claimed_sum: SecureField,
    range_claimed_sum: SecureField,
    wcell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
) -> Built {
    let decomp = FrameworkComponent::new(
        allocator,
        DecompEval::new(
            decomp_log_size(),
            crate::profile::ML_DSA_65,
            STREAM_ID_CTILDE_ABSORB,
            relations.clone(),
        ),
        decomp_claimed_sum,
    );
    // Standalone-only shared range table (C5): decomp draws its OWN `range`
    // relation independently (`DecompRelations::draw`), so it needs its own
    // matching provider here, not the hosted `SharedRangeTable` handle.
    let range = FrameworkComponent::new(
        allocator,
        RangeTableEval {
            relation: relations.range.clone(),
        },
        range_claimed_sum,
    );
    // wcell provider: YIELDS (−) the (w_bind_id, w) tuples decomp consumes.
    let wcell = FrameworkComponent::new(
        allocator,
        BalancerEval {
            log_size: wcell_log_size(),
            arity: crate::binding::WCELL_ARITY,
            relation: BalancerRelation::WCell(relations.wcell.clone()),
            sign_positive: false,
        },
        wcell_claimed_sum,
    );
    // hashio consumer: decomp YIELDS (+) each byte; the consumer requires (−) it.
    let hashio = FrameworkComponent::new(
        allocator,
        BalancerEval {
            log_size: hashio_log_size(),
            arity: crate::binding::HASH_IO_ARITY,
            relation: BalancerRelation::HashIo(relations.hash_io.clone()),
            sign_positive: false,
        },
        hashio_claimed_sum,
    );
    Built {
        decomp,
        range,
        wcell,
        hashio,
    }
}

fn module_trace_layout() -> Vec<u32> {
    let mut trace = vec![decomp_log_size(); N_BASE_COLS];
    trace.push(range_table_log_size()); // one multiplicity column
    // Each balancer writes `1 + arity` base columns (enabler + tuple cells).
    for _ in 0..crate::balancer::balancer_base_cols(crate::binding::WCELL_ARITY) {
        trace.push(wcell_log_size());
    }
    for _ in 0..crate::balancer::balancer_base_cols(crate::binding::HASH_IO_ARITY) {
        trace.push(hashio_log_size());
    }
    trace
}

fn module_interaction_layout() -> Vec<u32> {
    let mut inter = vec![decomp_log_size(); N_INTERACTION_COLS];
    for _ in 0..RANGE_TABLE_INTERACTION_COLS {
        inter.push(range_table_log_size());
    }
    for _ in 0..BALANCER_INTERACTION_COLS {
        inter.push(wcell_log_size());
    }
    for _ in 0..BALANCER_INTERACTION_COLS {
        inter.push(hashio_log_size());
    }
    inter
}

impl Air for DecompProver {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(DecompRelations::draw(channel));
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: all_preprocessed_log_sizes(),
            trace: module_trace_layout(),
            interaction: module_interaction_layout(),
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![
            self.decomp_claimed_sum,
            self.range_claimed_sum,
            self.wcell_claimed_sum,
            self.hashio_claimed_sum,
        ]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            self.relations.as_ref().expect("relations"),
            self.decomp_claimed_sum,
            self.range_claimed_sum,
            self.wcell_claimed_sum,
            self.hashio_claimed_sum,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").as_components()
    }
}

impl AirProver for DecompProver {
    fn max_log_size(&self) -> u32 {
        decomp_log_size()
            .max(range_table_log_size())
            .max(wcell_log_size())
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every constraint is degree ≤ 2 (each component needs its_log_size + 1);
        // the orchestrator sizes twiddles from the max over modules, so return the
        // largest (the range table at log 14 ⇒ 15). Each component still
        // declares its own exact +1 bound through `FrameworkEval`.
        self.max_log_size() + 1
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_all_preprocessed());
    }
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "mldsa_decomp",
            &all_preprocessed_ids(),
            &gen_all_preprocessed(),
        )
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut evals = gen_decomp_base_trace(&self.witness, decomp_log_size());
        #[cfg(test)]
        if let Some(checked_hint_total) = self.checked_hint_total {
            let final_row = crate::air_util::circle_row_to_coset(decomp_log_size())
                .iter()
                .position(|&coset| coset == N_ROWS - 1)
                .expect("final decomp row");
            evals[COL_HINT_ACC]
                .values
                .set(final_row, crate::air_util::m31(checked_hint_total));
        }
        #[cfg(test)]
        if let Some(poke) = self.trace_poke {
            apply_trace_poke(&mut evals, poke);
        }
        let metadata = self.gen_metadata();
        self.w1_encode_bytes = metadata.w1_encode_bytes;
        let range_mult = gen_range_table_multiplicities(range_uses_arrays(&metadata.rc_uses));
        self.range_mult = Some(range_mult.clone());
        evals.push(range_mult);
        // balancer base cols.
        evals.extend(gen_balancer_trace(
            wcell_log_size(),
            &wcell_tuples(&self.witness),
        ));
        evals.extend(gen_balancer_trace(
            hashio_log_size(),
            &hashio_tuples(&self.w1_encode_bytes),
        ));
        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let relations = self.relations.clone().expect("relations");
        let interaction = self.gen_interaction(&relations);
        let mut evals = interaction.trace;
        self.decomp_claimed_sum = interaction.claimed_sum;

        let (range_tr, range_sum) = gen_range_table_interaction(
            self.range_mult.as_ref().expect("range mult written"),
            &relations.range,
        );
        evals.extend(range_tr);
        self.range_claimed_sum = range_sum;
        // wcell provider yields (−); hashio consumer consumes (+).
        let (wtr, wsum) = gen_balancer_interaction(
            wcell_log_size(),
            &wcell_tuples(&self.witness),
            &BalancerRelation::WCell(relations.wcell.clone()),
            false,
        );
        self.wcell_claimed_sum = wsum;
        evals.extend(wtr);
        let (htr, hsum) = gen_balancer_interaction(
            hashio_log_size(),
            &hashio_tuples(&self.w1_encode_bytes),
            &BalancerRelation::HashIo(relations.hash_io.clone()),
            false,
        );
        self.hashio_claimed_sum = hsum;
        evals.extend(htr);

        tb.extend_evals(evals);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built.as_ref().expect("built").as_prover()
    }
}

impl Air for DecompVerifier {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(DecompRelations::draw(channel));
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: all_preprocessed_log_sizes(),
            trace: module_trace_layout(),
            interaction: module_interaction_layout(),
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![
            self.decomp_claimed_sum,
            self.range_claimed_sum,
            self.wcell_claimed_sum,
            self.hashio_claimed_sum,
        ]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            self.relations.as_ref().expect("relations"),
            self.decomp_claimed_sum,
            self.range_claimed_sum,
            self.wcell_claimed_sum,
            self.hashio_claimed_sum,
        ));
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        // Reconstruct tree-0 verifier-side for the pinned-root check in
        // `verify_decomp`. Same columns the prover commits (`gen_all_preprocessed`),
        // in `all_preprocessed_ids` order.
        Ok(gen_all_preprocessed())
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").as_components()
    }
}

pub fn prove_decomp(witness: MlDsaWitness, config: PcsConfig) -> Result<DecompProof, ProvingError> {
    let mut prover = DecompProver {
        witness,
        #[cfg(test)]
        checked_hint_total: None,
        #[cfg(test)]
        trace_poke: None,
        relations: None,
        decomp_claimed_sum: SecureField::zero(),
        range_claimed_sum: SecureField::zero(),
        wcell_claimed_sum: SecureField::zero(),
        hashio_claimed_sum: SecureField::zero(),
        range_mult: None,
        w1_encode_bytes: Vec::new(),
        built: None,
    };
    let stark_proof = air_core::prove(&mut [&mut prover], config)?;
    Ok(DecompProof {
        decomp_claimed_sum: prover.decomp_claimed_sum,
        range_claimed_sum: prover.range_claimed_sum,
        wcell_claimed_sum: prover.wcell_claimed_sum,
        hashio_claimed_sum: prover.hashio_claimed_sum,
        stark_proof,
    })
}

/// Verify a standalone decomp proof under the caller's exact PCS policy.
pub fn verify_decomp(
    proof: &DecompProof,
    expected_config: PcsConfig,
) -> Result<(), VerificationError> {
    if proof.stark_proof.config != expected_config {
        return Err(VerificationError::InvalidStructure(
            "mldsa_decomp: unexpected PCS configuration".into(),
        ));
    }
    let mut verifier = DecompVerifier {
        decomp_claimed_sum: proof.decomp_claimed_sum,
        range_claimed_sum: proof.range_claimed_sum,
        wcell_claimed_sum: proof.wcell_claimed_sum,
        hashio_claimed_sum: proof.hashio_claimed_sum,
        relations: None,
        built: None,
    };
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
                "mldsa_decomp: preprocessed root mismatch (forged tree-0)".into(),
            )
        }
    })
}

#[cfg(test)]
mod tests {
    use ml_dsa::signature::{Keypair, Signer};
    use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{assert_constraints_on_trace, FrameworkEval};

    use super::*;
    use crate::constants::{GAMMA2, K, N, OMEGA, Q};
    use crate::profile::ML_DSA_65;
    use crate::reference::decompose::{decompose, use_hint};
    use crate::reference::encoding::{pk_decode, sig_decode};
    use crate::reference::sponge::shake256;
    use crate::witness::generate_witness;
    use crate::MlDsaVerifyInput;

    fn pcs_config() -> PcsConfig {
        PcsConfig {
            fri_config: stwo::core::fri::FriConfig::new(0, 2, 3, 1),
            ..PcsConfig::default()
        }
    }

    fn witness() -> MlDsaWitness {
        let sk = SigningKey::<MlDsa65>::from_seed(&[0x42; 32].into());
        let vk = sk.verifying_key();
        let sig = sk.sign(b"mldsa-forged-hint-accumulator");
        let vk_bytes: EncodedVerifyingKey<MlDsa65> = vk.encode();
        let sig_bytes: EncodedSignature<MlDsa65> = sig.encode();
        let pk = pk_decode(ML_DSA_65, vk_bytes.as_slice()).expect("pk_decode");
        let sig = sig_decode(ML_DSA_65, sig_bytes.as_slice()).expect("sig_decode");
        let (tr, _) = shake256(&[vk_bytes.as_slice()], 64);
        let mut tr_array = [0u8; 64];
        tr_array.copy_from_slice(&tr);
        let input = MlDsaVerifyInput::from_decoded(
            ML_DSA_65,
            &pk,
            &sig,
            tr_array,
            b"mldsa-forged-hint-accumulator".to_vec(),
        );
        generate_witness(ML_DSA_65, &input).expect("honest witness")
    }

    fn witness_with_first_w(w_value: u32, hint: u8) -> MlDsaWitness {
        let mut witness = witness();
        for i in 0..K {
            for m in 0..N {
                let (w1, w0) = decompose(ML_DSA_65, witness.rows[i].w[m]);
                witness.decomp.w0[i][m] = w0;
                witness.decomp.hint[i][m] = 0;
                witness.decomp.w1[i][m] = w1 as u32;
            }
            witness.decomp.hint_weight[i] = 0;
        }

        let (w1, w0) = decompose(ML_DSA_65, w_value);
        witness.rows[0].w[0] = w_value;
        witness.decomp.w0[0][0] = w0;
        witness.decomp.hint[0][0] = hint;
        witness.decomp.w1[0][0] = use_hint(ML_DSA_65, hint, w_value) as u32;
        witness.decomp.hint_weight[0] = hint as usize;
        assert_eq!(w1, decompose(ML_DSA_65, witness.rows[0].w[0]).0);
        witness
    }

    fn boundary_witness() -> MlDsaWitness {
        let witness = witness_with_first_w(Q - GAMMA2, 1);
        assert_eq!(
            decompose(ML_DSA_65, witness.rows[0].w[0]),
            (0, -(GAMMA2 as i32))
        );
        assert_eq!(witness.decomp.w0[0][0], -(GAMMA2 as i32));
        assert_eq!(witness.decomp.w1[0][0], 15);
        witness
    }

    fn assert_decomp_constraints_for(witness: &MlDsaWitness) {
        let relations = DecompRelations::dummy();
        let interaction = gen_decomp_interaction(
            witness,
            decomp_log_size(),
            STREAM_ID_CTILDE_ABSORB,
            &relations,
        );
        let trace = TreeVec::new(vec![
            crate::decomp::gen_decomp_preprocessed(ML_DSA_65, decomp_log_size()),
            gen_decomp_base_trace(witness, decomp_log_size()),
            interaction.trace,
        ]);
        let trace = trace.as_ref().map_cols(|column| column.to_cpu().values);
        let trace = trace.as_cols_ref();
        let component = DecompEval::new(
            decomp_log_size(),
            ML_DSA_65,
            STREAM_ID_CTILDE_ABSORB,
            relations,
        );
        assert_constraints_on_trace(
            &trace,
            decomp_log_size(),
            |eval| {
                component.evaluate(eval);
            },
            interaction.claimed_sum,
        );
    }

    fn prove_with_test_options(
        witness: MlDsaWitness,
        checked_hint_total: Option<u32>,
        trace_poke: Option<DecompTracePoke>,
    ) -> Result<DecompProof, ProvingError> {
        let mut prover = DecompProver {
            witness,
            checked_hint_total,
            trace_poke,
            relations: None,
            decomp_claimed_sum: SecureField::zero(),
            range_claimed_sum: SecureField::zero(),
            wcell_claimed_sum: SecureField::zero(),
            hashio_claimed_sum: SecureField::zero(),
            range_mult: None,
            w1_encode_bytes: Vec::new(),
            built: None,
        };
        let stark_proof = air_core::prove(&mut [&mut prover], pcs_config())?;
        Ok(DecompProof {
            decomp_claimed_sum: prover.decomp_claimed_sum,
            range_claimed_sum: prover.range_claimed_sum,
            wcell_claimed_sum: prover.wcell_claimed_sum,
            hashio_claimed_sum: prover.hashio_claimed_sum,
            stark_proof,
        })
    }

    #[test]
    fn fips_wrap_boundary_constraints_pass() {
        assert_decomp_constraints_for(&boundary_witness());
    }

    #[test]
    fn fips_wrap_boundary_standalone_proves_and_verifies() {
        let proof = prove_decomp(boundary_witness(), pcs_config()).expect("boundary must prove");
        verify_decomp(&proof, pcs_config()).expect("boundary proof must verify");
    }

    #[test]
    fn decomp_boundary_requires_zero_w1() {
        let witness = witness_with_first_w(GAMMA2, 0);
        assert!(
            matches!(
                prove_with_test_options(
                    witness,
                    None,
                    Some(DecompTracePoke::BoundaryWithNonzeroW1),
                ),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "(w1,w0)=(1,−γ2) must be rejected even though it reconstructs w=+γ2"
        );
    }

    #[test]
    fn decomp_below_negative_gamma2_rejects() {
        let witness = witness_with_first_w(Q - GAMMA2 - 1, 0);
        assert!(
            matches!(
                prove_with_test_options(witness, None, Some(DecompTracePoke::BelowNegativeGamma2),),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "w0=−γ2−1 must be rejected by the shifted lower range"
        );
    }

    /// C8c(b) negative: with the `v·v_inv` boundary equation deleted, `b·v=0`
    /// and `b·w1=0` alone must still reject the FIPS-boundary noncanonical
    /// twin (w1,w0)=(1,−γ2) when the zero flag is left UNSET (b=0) rather
    /// than forced to 1. Both remaining equations are trivially satisfied
    /// (v=0, b=0), so only the shifted lower range value a=v−1+b=−1 catches
    /// it, via an Rc13/Rc7 lookup imbalance (no provider row for a negative
    /// value).
    #[test]
    fn decomp_boundary_zero_flag_unset_rejects() {
        let witness = witness_with_first_w(GAMMA2, 0);
        assert!(
            matches!(
                prove_with_test_options(
                    witness,
                    None,
                    Some(DecompTracePoke::BoundaryZeroFlagUnset),
                ),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "(w1,w0)=(1,−γ2) with the zero flag left unset must still be \
             rejected, via the a-range check rather than a direct b·w1 \
             failure"
        );
    }

    /// C8c(b) negative: a non-boolean zero flag (b=2) at the same FIPS
    /// boundary with a nonzero w1 must be rejected directly by `b·w1=0`
    /// (2·w1≠0) -- demonstrating the deleted booleanity constraint on b was
    /// never load-bearing for this gate.
    #[test]
    fn decomp_non_boolean_zero_flag_rejects() {
        let witness = witness_with_first_w(GAMMA2, 0);
        assert!(
            matches!(
                prove_with_test_options(
                    witness,
                    None,
                    Some(DecompTracePoke::NonBooleanZeroFlagWithNonzeroW1),
                ),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "a non-boolean zero flag (b=2) with nonzero w1 must be rejected \
             by b·w1=0"
        );
    }

    /// C5(4) -- the arity trap: `w1'` poked to 2000 (an Rc11-magnitude value)
    /// with `wrap_m` recomputed so the UseHint equation still holds exactly.
    /// Decomp always tags its w1' lookup with `RcKind::Rc4`'s bound id;
    /// 2000 is a legitimate value elsewhere in the shared table (under
    /// `RcKind::Rc11`'s bound id), but claiming it under Rc4's bound id must
    /// still be rejected -- there is no provider row for that exact
    /// `(value, bound_id)` tuple.
    #[test]
    fn decomp_rc11_magnitude_rejected_under_rc4_bound_id() {
        let witness = witness_with_first_w(GAMMA2, 0);
        assert!(
            matches!(
                prove_with_test_options(
                    witness,
                    None,
                    Some(DecompTracePoke::Rc11MagnitudeClaimedUnderRc4BoundId),
                ),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "w1'=2000 claimed under Rc4's bound id must be rejected even \
             though 2000 is valid under Rc11's bound id"
        );
    }

    /// The UseHint forgery that an unconstrained `wrap_m` would enable, and
    /// the reason the `wrap_m + 1` Rc4 lookup exists. `w1'` is poked to 7 --
    /// fully inside Rc4's domain, so its own lookup still matches -- while
    /// `wrap_m = 7·16⁻¹ mod p = 939_524_096` keeps the linear UseHint
    /// constraint satisfied. Since `w1'` is packed into the c-tilde sponge,
    /// accepting such a witness would be a universal forgery: the prover picks
    /// the w1Encode preimage independently of the real commitment `w`.
    ///
    /// NOT AN ISOLATING REGRESSION TEST. Mutation-checked 2026-08-06: with the
    /// `wrap_m` lookup removed (and its use/census removed, i.e. a true revert
    /// to the broken state) this poke is STILL rejected, so some other
    /// constraint in this harness also catches it and the test does not prove
    /// the lookup is what stops the attack. The lookup's necessity rests on
    /// the algebra in the module doc, not on this test. An isolating test needs
    /// a poke that is consistent across every other constraint (notably the
    /// w1Encode byte packing and the metadata use-census) -- open work item.
    #[test]
    fn decomp_in_range_w1p_via_unconstrained_wrap_m_is_rejected() {
        let witness = witness_with_first_w(GAMMA2, 0);
        assert!(
            matches!(
                prove_with_test_options(
                    witness,
                    None,
                    Some(DecompTracePoke::InRangeW1pViaUnconstrainedWrapM),
                ),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "an in-Rc4-range w1' backed by a modular-inverse wrap_m must be \
             rejected by the wrap_m range check"
        );
    }

    #[test]
    fn forged_hint_accumulator_split_is_rejected() {
        let mut witness = witness();
        let target = OMEGA + 1;
        let mut total: usize = witness
            .decomp
            .hint
            .iter()
            .flatten()
            .map(|&hint| hint as usize)
            .sum();
        'fill: for i in 0..K {
            for m in 0..N {
                if total == target {
                    break 'fill;
                }
                if witness.decomp.hint[i][m] == 0 {
                    witness.decomp.hint[i][m] = 1;
                    witness.decomp.w1[i][m] = use_hint(ML_DSA_65, 1, witness.rows[i].w[m]) as u32;
                    total += 1;
                }
            }
        }
        assert_eq!(total, target, "fixture must have exactly ω+1 hints");

        let metadata = gen_decomp_metadata_with_test_options(&witness, Some(OMEGA as u32), None);
        let interaction = gen_decomp_interaction_with_test_options(
            &witness,
            decomp_log_size(),
            STREAM_ID_CTILDE_ABSORB,
            &DecompRelations::dummy(),
            Some(OMEGA as u32),
            None,
        );
        for kind in RcKind::ALL {
            assert_eq!(
                metadata.rc_uses.for_kind(kind),
                interaction.rc_uses.for_kind(kind),
                "checked hint metadata mismatch for {kind:?}"
            );
        }
        assert_eq!(
            metadata.w1_encode_bytes, interaction.w1_encode_bytes,
            "checked hint metadata must preserve w1Encode bytes"
        );

        assert!(
            matches!(
                prove_with_test_options(witness, Some(OMEGA as u32), None),
                Err(ProvingError::ConstraintsNotSatisfied)
            ),
            "the final base hint accumulator must equal the true interaction sum"
        );
    }
}
