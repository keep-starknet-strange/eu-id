//! Standalone prove/verify for `mldsa_decomp` through the `air-core` orchestrator
//! (mirrors `crate::proof`). The module contributes, in commit order:
//!   1. `decomp`             — the [DECOMP]+[HINT] byte-pair component.
//!   2. rc providers          — rc4, rc13, rc7, rc8 (one each).
//!   3. `wcell_provider`      — TEST-SIDE balancer: yields the `(w_bind_id, w)`
//!      tuples decomp consumes (stands in for the coeffs W-cell yields; M6 wires
//!      the real coeffs component here instead).
//!   4. `hashio_consumer`     — TEST-SIDE balancer: consumes the 768 `w1Encode`
//!      bytes decomp yields (stands in for the sponge absorb side; M6 wires it).
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
#[cfg(test)]
use stwo::prover::backend::Column;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use crate::air_util::{padded_log_size, ColEval};
use crate::binding::STREAM_ID_CTILDE_ABSORB;
use crate::witness::MlDsaWitness;

use super::relations::DecompRelations;
use super::tables::{
    gen_table_interaction, gen_table_multiplicities, gen_table_preprocessed, RcKind, RcTableEval,
    RC_TABLE_INTERACTION_COLS,
};
use super::{
    decomp_preprocessed_ids, gen_decomp_base_trace, gen_decomp_interaction,
    gen_decomp_preprocessed, DecompEval, N_BASE_COLS, N_INTERACTION_COLS, N_PAIRS,
};
#[cfg(test)]
use super::{gen_decomp_interaction_with_checked_hint_total, COL_HINT_ACC};
use crate::balancer::{
    gen_balancer_interaction, gen_balancer_trace, BalancerEval, BalancerRelation,
    BALANCER_INTERACTION_COLS,
};

const N_RC: usize = 4;

/// The public statement + prover claims of a decomp proof.
pub struct DecompProof {
    pub decomp_claimed_sum: SecureField,
    pub rc_claimed_sums: [SecureField; N_RC],
    pub wcell_claimed_sum: SecureField,
    pub hashio_claimed_sum: SecureField,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

fn decomp_log_size() -> u32 {
    padded_log_size(N_PAIRS)
}

fn all_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = decomp_preprocessed_ids();
    for kind in RcKind::ALL {
        ids.push(kind.value_column_id());
    }
    ids
}

fn all_preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = vec![decomp_log_size(); decomp_preprocessed_ids().len()];
    for kind in RcKind::ALL {
        sizes.push(kind.log_size());
    }
    sizes
}

fn gen_all_preprocessed() -> Vec<ColEval> {
    let mut cols = gen_decomp_preprocessed(decomp_log_size());
    for kind in RcKind::ALL {
        cols.push(gen_table_preprocessed(kind));
    }
    cols
}

// The two balancer components' log sizes (padded to their tuple counts).
fn wcell_log_size() -> u32 {
    padded_log_size(crate::constants::K * crate::constants::N) // 1536
}
fn hashio_log_size() -> u32 {
    padded_log_size(N_PAIRS) // 768
}

struct Built {
    decomp: FrameworkComponent<DecompEval>,
    rc: Vec<FrameworkComponent<RcTableEval>>,
    wcell: FrameworkComponent<BalancerEval>,
    hashio: FrameworkComponent<BalancerEval>,
}

impl Built {
    fn as_components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.decomp];
        out.extend(self.rc.iter().map(|c| c as &dyn Component));
        out.push(&self.wcell);
        out.push(&self.hashio);
        out
    }
    fn as_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = vec![&self.decomp];
        out.extend(
            self.rc
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.push(&self.wcell);
        out.push(&self.hashio);
        out
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
    relations: Option<DecompRelations>,
    decomp_claimed_sum: SecureField,
    rc_claimed_sums: [SecureField; N_RC],
    wcell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    rc_mult: Vec<ColEval>,
    w1_encode_bytes: Vec<u8>,
    built: Option<Built>,
}

impl DecompProver {
    fn gen_interaction(&self, relations: &DecompRelations) -> super::DecompInteraction {
        #[cfg(test)]
        if let Some(checked_hint_total) = self.checked_hint_total {
            return gen_decomp_interaction_with_checked_hint_total(
                &self.witness,
                decomp_log_size(),
                STREAM_ID_CTILDE_ABSORB,
                relations,
                checked_hint_total,
            );
        }
        gen_decomp_interaction(
            &self.witness,
            decomp_log_size(),
            STREAM_ID_CTILDE_ABSORB,
            relations,
        )
    }
}

struct DecompVerifier {
    decomp_claimed_sum: SecureField,
    rc_claimed_sums: [SecureField; N_RC],
    wcell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
    relations: Option<DecompRelations>,
    built: Option<Built>,
}

fn build_components(
    allocator: &mut TraceLocationAllocator,
    relations: &DecompRelations,
    decomp_claimed_sum: SecureField,
    rc_claimed_sums: &[SecureField; N_RC],
    wcell_claimed_sum: SecureField,
    hashio_claimed_sum: SecureField,
) -> Built {
    let decomp = FrameworkComponent::new(
        allocator,
        DecompEval {
            log_size: decomp_log_size(),
            ct_stream: STREAM_ID_CTILDE_ABSORB,
            relations: relations.clone(),
        },
        decomp_claimed_sum,
    );
    let mut rc = Vec::with_capacity(N_RC);
    for (idx, kind) in RcKind::ALL.iter().enumerate() {
        rc.push(FrameworkComponent::new(
            allocator,
            RcTableEval {
                kind: *kind,
                relation: rc_relation(relations, *kind).clone(),
            },
            rc_claimed_sums[idx],
        ));
    }
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
        rc,
        wcell,
        hashio,
    }
}

fn rc_relation(r: &DecompRelations, kind: RcKind) -> &super::relations::RcRelation {
    match kind {
        RcKind::Rc4 => &r.rc4,
        RcKind::Rc13 => &r.rc13,
        RcKind::Rc7 => &r.rc7,
        RcKind::Rc8 => &r.rc8,
    }
}

fn module_trace_layout() -> Vec<u32> {
    let mut trace = vec![decomp_log_size(); N_BASE_COLS];
    for kind in RcKind::ALL {
        trace.push(kind.log_size()); // one multiplicity column each
    }
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
    for kind in RcKind::ALL {
        for _ in 0..RC_TABLE_INTERACTION_COLS {
            inter.push(kind.log_size());
        }
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
        let mut s = vec![self.decomp_claimed_sum];
        s.extend(self.rc_claimed_sums);
        s.push(self.wcell_claimed_sum);
        s.push(self.hashio_claimed_sum);
        s
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            self.relations.as_ref().expect("relations"),
            self.decomp_claimed_sum,
            &self.rc_claimed_sums,
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
            .max(RcKind::Rc13.log_size())
            .max(wcell_log_size())
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every constraint is degree ≤ 2 (each component needs its_log_size + 1);
        // the orchestrator sizes twiddles from the max over modules, so return the
        // largest (rc13 at log 13 ⇒ 14). Each component still declares its own
        // exact +1 bound (the M4 Horner-mask trap) via `FrameworkEval`.
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
                .position(|&coset| coset == N_PAIRS - 1)
                .expect("final decomp row");
            evals[COL_HINT_ACC]
                .values
                .set(final_row, crate::air_util::m31(checked_hint_total));
        }
        // rc multiplicities from a dry-run interaction (relations not needed).
        let dry = self.gen_interaction(&DecompRelations::dummy());
        self.w1_encode_bytes = dry.w1_encode_bytes.clone();
        self.rc_mult = RcKind::ALL
            .iter()
            .map(|kind| gen_table_multiplicities(*kind, dry.rc_uses.for_kind(*kind)))
            .collect();
        evals.extend(self.rc_mult.clone());
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

        for (idx, kind) in RcKind::ALL.iter().enumerate() {
            let (tr, sum) =
                gen_table_interaction(*kind, &self.rc_mult[idx], rc_relation(&relations, *kind));
            evals.extend(tr);
            self.rc_claimed_sums[idx] = sum;
        }
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
        let mut s = vec![self.decomp_claimed_sum];
        s.extend(self.rc_claimed_sums);
        s.push(self.wcell_claimed_sum);
        s.push(self.hashio_claimed_sum);
        s
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            self.relations.as_ref().expect("relations"),
            self.decomp_claimed_sum,
            &self.rc_claimed_sums,
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
        relations: None,
        decomp_claimed_sum: SecureField::zero(),
        rc_claimed_sums: [SecureField::zero(); N_RC],
        wcell_claimed_sum: SecureField::zero(),
        hashio_claimed_sum: SecureField::zero(),
        rc_mult: Vec::new(),
        w1_encode_bytes: Vec::new(),
        built: None,
    };
    let stark_proof = air_core::prove(&mut [&mut prover], config)?;
    Ok(DecompProof {
        decomp_claimed_sum: prover.decomp_claimed_sum,
        rc_claimed_sums: prover.rc_claimed_sums,
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
        rc_claimed_sums: proof.rc_claimed_sums,
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

    use super::*;
    use crate::constants::{K, N, OMEGA};
    use crate::reference::decompose::use_hint;
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
        let pk = pk_decode(vk_bytes.as_slice()).expect("pk_decode");
        let sig = sig_decode(sig_bytes.as_slice()).expect("sig_decode");
        let (tr, _) = shake256(&[vk_bytes.as_slice()], 64);
        let mut tr_array = [0u8; 64];
        tr_array.copy_from_slice(&tr);
        let input = MlDsaVerifyInput::from_decoded(
            &pk,
            &sig,
            tr_array,
            b"mldsa-forged-hint-accumulator".to_vec(),
        );
        generate_witness(&input).expect("honest witness")
    }

    fn prove_with_checked_hint_total(
        witness: MlDsaWitness,
        checked_hint_total: u32,
    ) -> Result<DecompProof, ProvingError> {
        let mut prover = DecompProver {
            witness,
            checked_hint_total: Some(checked_hint_total),
            relations: None,
            decomp_claimed_sum: SecureField::zero(),
            rc_claimed_sums: [SecureField::zero(); N_RC],
            wcell_claimed_sum: SecureField::zero(),
            hashio_claimed_sum: SecureField::zero(),
            rc_mult: Vec::new(),
            w1_encode_bytes: Vec::new(),
            built: None,
        };
        let stark_proof = air_core::prove(&mut [&mut prover], pcs_config())?;
        Ok(DecompProof {
            decomp_claimed_sum: prover.decomp_claimed_sum,
            rc_claimed_sums: prover.rc_claimed_sums,
            wcell_claimed_sum: prover.wcell_claimed_sum,
            hashio_claimed_sum: prover.hashio_claimed_sum,
            stark_proof,
        })
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
                    witness.decomp.w1[i][m] = use_hint(1, witness.rows[i].w[m]) as u32;
                    total += 1;
                }
            }
        }
        assert_eq!(total, target, "fixture must have exactly ω+1 hints");

        assert!(matches!(
            prove_with_checked_hint_total(witness, OMEGA as u32),
            Err(ProvingError::ConstraintsNotSatisfied)
        ),
        "the final base hint accumulator must equal the true interaction sum"
        );
    }
}
