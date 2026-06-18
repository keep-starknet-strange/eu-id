//! The digest-bind bridge as a self-contained [`air_core`] proving module.
//!
//! This wraps three components — the [`DigestBindComponent`] and the two
//! range-check providers it consumes (bytes to `[0,256)`, carries to `[0,2^13)`)
//! — behind one `Air`/`AirProver`, so the combined prover drives it as a sibling
//! module alongside P256 and SHA. It draws its own range relations; it receives
//! the two cross-module relations it consumes via shared handles:
//!
//! - `ScalarZRelation` — provided **analytically** by P256
//!   ([`super::scalar_z_provider_claimed_sum`]); pins the bridge's `z` to the
//!   proven ECDSA `z`.
//! - `Sha256Digest` (`DigestBytesRelation`) — provided by the SHA module's
//!   final-block yield; pins the bridge's 32 bytes to `SHA-256(C)`.
//!
//! The module's own claimed sum is therefore exactly
//! `+1/combine(scalar_z) + 1/combine(digest)` (the two range channels cancel
//! internally), which the global balance cancels against P256's and SHA's
//! provider terms — so the combined proof verifies **iff** the signed digest,
//! the hashed preimage's digest, and the ECDSA `z` are all the same 32 bytes.
//!
//! The range tables are **namespaced** (`digest_bind_*`) rather than reusing the
//! generic `p256_range{k}_value` ids, so the carry table does not alias P256's
//! own `range13` table in the shared `TraceLocationAllocator` (interface-contract
//! item 5).

use air_core::relations::DigestBytesRelation;
use air_core::{Air, AirProver, TreeLayout};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry, TraceLocationAllocator,
};

use crate::range_checks::{
    ColumnEval, RangeCheckClaim, RangeCheckInteractionClaim, RangeCheckRelation,
};

use super::air::{digest_bind_lookups, DigestBindComponent, DigestBindEval};
use super::witness::{
    gen_base_trace, gen_interaction_trace, range_uses, DigestBindRelations, DigestBindRow,
};
use super::{ScalarZRelation, SharedScalarZRelation, TOTAL_COLS};
use air_core::relations::SharedRelation;

const EXT: usize = SECURE_EXTENSION_DEGREE;

/// Bit width of the byte range table (`[0, 256)`).
const BYTE_RANGE_BITS: u32 = 8;
/// Bit width of the carry range table (`[0, 2^13)`; carries are `< 2^13`).
const CARRY_RANGE_BITS: u32 = 13;

fn byte_range_value_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "digest_bind_byte_range_value".to_string(),
    }
}
fn carry_range_value_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "digest_bind_carry_range_value".to_string(),
    }
}

/// A range-check provider identical to [`crate::range_checks::RangeCheckEval`]
/// but reading a **caller-chosen** preprocessed id, so the bridge's tables do not
/// alias P256's generic `p256_range{k}_value` ids in the shared allocator.
#[derive(Clone, Debug)]
struct NamespacedRangeEval {
    relation: RangeCheckRelation,
    log_size: u32,
    value_id: PreProcessedColumnId,
}

impl FrameworkEval for NamespacedRangeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(self.value_id.clone());
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            &[value],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

type NamespacedRangeComponent = FrameworkComponent<NamespacedRangeEval>;

/// Number of base-field interaction columns produced by `n_lookups` lookups
/// under solo batching (one fraction per column, matching `finalize_logup`):
/// `n` secure columns × `SECURE_EXTENSION_DEGREE`.
fn interaction_base_cols(n_lookups: usize) -> usize {
    n_lookups * EXT
}

/// The three claimed sums the bridge module commits, in component (commit) order.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DigestBindInteractionClaim {
    pub digest_bind: QM31,
    pub byte_range: QM31,
    pub carry_range: QM31,
}

impl DigestBindInteractionClaim {
    fn flatten(&self) -> Vec<QM31> {
        vec![self.digest_bind, self.byte_range, self.carry_range]
    }
}

fn layout(log_size: u32) -> TreeLayout {
    // Preprocessed: the two namespaced range value tables.
    let preprocessed = vec![BYTE_RANGE_BITS, CARRY_RANGE_BITS];
    // Trace: digest_bind's 85 columns at `log_size`, then one multiplicity column
    // per range table at the table's own log size.
    let mut trace = vec![log_size; TOTAL_COLS];
    trace.push(BYTE_RANGE_BITS);
    trace.push(CARRY_RANGE_BITS);
    // Interaction: digest_bind's paired logup columns at `log_size`, then one
    // logup column per range table (1 lookup each) at the table's log size.
    let mut interaction = vec![log_size; interaction_base_cols(digest_bind_lookups(true))];
    interaction.extend(std::iter::repeat_n(
        BYTE_RANGE_BITS,
        interaction_base_cols(1),
    ));
    interaction.extend(std::iter::repeat_n(
        CARRY_RANGE_BITS,
        interaction_base_cols(1),
    ));
    TreeLayout {
        preprocessed,
        trace,
        interaction,
    }
}

/// The relations the bridge module draws itself in `draw_relations`: the two
/// range tables. (The two cross-module relations it consumes — `ScalarZ` and the
/// digest — are read from shared handles at component-build time, not held here.)
struct DrawnRelations {
    byte_range: RangeCheckRelation,
    carry_range: RangeCheckRelation,
}

/// Aggregate of the three built components, in commit order.
struct DigestBindComponents {
    digest_bind: DigestBindComponent,
    byte_range: NamespacedRangeComponent,
    carry_range: NamespacedRangeComponent,
}

impl DigestBindComponents {
    fn build(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        relations: &DrawnRelations,
        scalar_z: ScalarZRelation,
        digest: DigestBytesRelation,
        claim: &DigestBindInteractionClaim,
    ) -> Self {
        let digest_bind = DigestBindComponent::new(
            allocator,
            DigestBindEval {
                log_size,
                range8: relations.byte_range.clone(),
                range13: relations.carry_range.clone(),
                scalar_z,
                digest,
                expose_digest: true,
            },
            claim.digest_bind,
        );
        let byte_range = NamespacedRangeComponent::new(
            allocator,
            NamespacedRangeEval {
                relation: relations.byte_range.clone(),
                log_size: BYTE_RANGE_BITS,
                value_id: byte_range_value_id(),
            },
            claim.byte_range,
        );
        let carry_range = NamespacedRangeComponent::new(
            allocator,
            NamespacedRangeEval {
                relation: relations.carry_range.clone(),
                log_size: CARRY_RANGE_BITS,
                value_id: carry_range_value_id(),
            },
            claim.carry_range,
        );
        Self {
            digest_bind,
            byte_range,
            carry_range,
        }
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![&self.digest_bind, &self.byte_range, &self.carry_range]
    }

    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.digest_bind, &self.byte_range, &self.carry_range]
    }
}

fn preprocessed_ids() -> Vec<PreProcessedColumnId> {
    vec![byte_range_value_id(), carry_range_value_id()]
}

/// Prover-side bridge module.
pub struct DigestBindProver {
    rows: Vec<DigestBindRow>,
    log_size: u32,
    scalar_z_handle: SharedScalarZRelation,
    digest_handle: SharedRelation<DigestBytesRelation>,
    relations: Option<DrawnRelations>,
    interaction_claim: Option<DigestBindInteractionClaim>,
    components: Option<DigestBindComponents>,
}

impl DigestBindProver {
    /// Build the module from the per-signature `(sig_id, z)` rows and the two
    /// shared handles the orchestrator wires (P256's `ScalarZ`, SHA's digest).
    pub fn new(
        rows: Vec<DigestBindRow>,
        log_size: u32,
        scalar_z_handle: SharedScalarZRelation,
        digest_handle: SharedRelation<DigestBytesRelation>,
    ) -> Self {
        Self {
            rows,
            log_size,
            scalar_z_handle,
            digest_handle,
            relations: None,
            interaction_claim: None,
            components: None,
        }
    }

    pub fn interaction_claim(&self) -> &DigestBindInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("interaction claim is set during the interaction phase")
    }

    fn relations(&self) -> &DrawnRelations {
        self.relations
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &DigestBindComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for DigestBindProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.log_size as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(DrawnRelations {
            byte_range: RangeCheckRelation::draw(channel),
            carry_range: RangeCheckRelation::draw(channel),
        });
    }

    fn layout(&self) -> TreeLayout {
        layout(self.log_size)
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.interaction_claim().flatten()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        self.components = Some(DigestBindComponents::build(
            allocator,
            self.log_size,
            self.relations(),
            self.scalar_z_handle.get(),
            self.digest_handle.get(),
            &claim,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for DigestBindProver {
    fn max_log_size(&self) -> u32 {
        // The carry range table (`2^13`) is the largest committed domain.
        CARRY_RANGE_BITS.max(self.log_size)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every component is degree 2 (`log_size + 1`); the carry range table's
        // own `log_size` (13) dominates.
        (self.log_size + 1)
            .max(BYTE_RANGE_BITS + 1)
            .max(CARRY_RANGE_BITS + 1)
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let byte_table = RangeCheckClaim::new(BYTE_RANGE_BITS).gen_preprocessed_column();
        let carry_table = RangeCheckClaim::new(CARRY_RANGE_BITS).gen_preprocessed_column();
        tb.extend_evals(vec![byte_table, carry_table]);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut cols: Vec<ColumnEval> = gen_base_trace(&self.rows, self.log_size);
        let (byte_uses, carry_uses) = range_uses(&self.rows);
        cols.push(RangeCheckClaim::new(BYTE_RANGE_BITS).gen_multiplicity_trace(byte_uses));
        cols.push(RangeCheckClaim::new(CARRY_RANGE_BITS).gen_multiplicity_trace(carry_uses));
        tb.extend_evals(cols);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let relations = self.relations();
        let scalar_z = self.scalar_z_handle.get();
        let digest = self.digest_handle.get();

        let base = gen_base_trace(&self.rows, self.log_size);
        let bridge_relations = DigestBindRelations {
            range8: &relations.byte_range,
            range13: &relations.carry_range,
            scalar_z: &scalar_z,
            digest: &digest,
        };
        let (digest_bind_cols, digest_bind_sum) =
            gen_interaction_trace(&base, &bridge_relations, true);

        let (byte_uses, carry_uses) = range_uses(&self.rows);
        let byte_value = RangeCheckClaim::new(BYTE_RANGE_BITS).gen_preprocessed_column();
        let byte_mult = RangeCheckClaim::new(BYTE_RANGE_BITS).gen_multiplicity_trace(byte_uses);
        let (byte_cols, byte_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
            &byte_mult,
            &byte_value,
            &relations.byte_range,
        );
        let carry_value = RangeCheckClaim::new(CARRY_RANGE_BITS).gen_preprocessed_column();
        let carry_mult = RangeCheckClaim::new(CARRY_RANGE_BITS).gen_multiplicity_trace(carry_uses);
        let (carry_cols, carry_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
            &carry_mult,
            &carry_value,
            &relations.carry_range,
        );

        let mut cols = digest_bind_cols;
        cols.extend(byte_cols);
        cols.extend(carry_cols);
        tb.extend_evals(cols);

        self.interaction_claim = Some(DigestBindInteractionClaim {
            digest_bind: digest_bind_sum,
            byte_range: byte_claim.claimed_sum,
            carry_range: carry_claim.claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built_components().component_provers()
    }
}

/// Verifier-side bridge module: reconstructs the same components from the proof's
/// claimed sums and the shared handles.
pub struct DigestBindVerifier {
    log_size: u32,
    scalar_z_handle: SharedScalarZRelation,
    digest_handle: SharedRelation<DigestBytesRelation>,
    interaction_claim: DigestBindInteractionClaim,
    relations: Option<DrawnRelations>,
    components: Option<DigestBindComponents>,
}

impl DigestBindVerifier {
    pub fn new(
        log_size: u32,
        interaction_claim: DigestBindInteractionClaim,
        scalar_z_handle: SharedScalarZRelation,
        digest_handle: SharedRelation<DigestBytesRelation>,
    ) -> Self {
        Self {
            log_size,
            scalar_z_handle,
            digest_handle,
            interaction_claim,
            relations: None,
            components: None,
        }
    }

    fn relations(&self) -> &DrawnRelations {
        self.relations
            .as_ref()
            .expect("relations are drawn before they are used")
    }

    fn built_components(&self) -> &DigestBindComponents {
        self.components
            .as_ref()
            .expect("components are built before they are borrowed")
    }
}

impl Air for DigestBindVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.log_size as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(DrawnRelations {
            byte_range: RangeCheckRelation::draw(channel),
            carry_range: RangeCheckRelation::draw(channel),
        });
    }

    fn layout(&self) -> TreeLayout {
        layout(self.log_size)
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.interaction_claim.flatten()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(DigestBindComponents::build(
            allocator,
            self.log_size,
            self.relations(),
            self.scalar_z_handle.get(),
            self.digest_handle.get(),
            &self.interaction_claim,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::components::digest_bind::{
        scalar_z_provider_claimed_sum, z_digest_byte_witness, DIGEST_BYTES,
    };
    use crate::field::limbs::P256M31BigInt;
    use crate::public_inputs::PublicEcdsaInstance;
    use crate::types::U256;
    use stwo::core::fields::m31::M31;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::PcsConfig;
    use stwo_constraint_framework::Relation;

    /// A synthetic, trace-less module that plays the role of P256 (analytic
    /// `ScalarZ` provider) and SHA (analytic digest provider) at once: it draws
    /// both shared relations, sets the handles, and yields `−1/combine` of each —
    /// exactly the two terms the real provider modules contribute. Lets the
    /// bridge module's full prove/verify path be exercised in isolation.
    struct AnalyticProviders {
        instances: Vec<PublicEcdsaInstance<M31>>,
        digest_bytes: [M31; DIGEST_BYTES],
        scalar_z_handle: SharedScalarZRelation,
        digest_handle: SharedRelation<DigestBytesRelation>,
        scalar_z: Option<ScalarZRelation>,
        digest: Option<DigestBytesRelation>,
    }

    impl Air for AnalyticProviders {
        fn mix_public(&self, _channel: &mut Blake2sChannel) {}

        fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
            let scalar_z = ScalarZRelation::draw(channel);
            let digest = DigestBytesRelation::draw(channel);
            self.scalar_z_handle.set(scalar_z.clone());
            self.digest_handle.set(digest.clone());
            self.scalar_z = Some(scalar_z);
            self.digest = Some(digest);
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![],
                trace: vec![],
                interaction: vec![],
            }
        }

        fn claimed_sums(&self) -> Vec<QM31> {
            let scalar_z = self.scalar_z.as_ref().expect("drawn");
            let digest = self.digest.as_ref().expect("drawn");
            let scalar_z_sum = scalar_z_provider_claimed_sum(&self.instances, scalar_z);
            let values = self.digest_bytes.to_vec();
            let denom: SecureField = digest.combine(&values);
            let digest_sum = -SecureField::from(M31::from_u32_unchecked(1)) / denom;
            vec![scalar_z_sum, digest_sum]
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![]
        }

        fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

        fn components(&self) -> Vec<&dyn Component> {
            vec![]
        }
    }

    impl AirProver for AnalyticProviders {
        fn max_log_size(&self) -> u32 {
            1
        }
        fn max_constraint_log_degree_bound(&self) -> u32 {
            2
        }
        fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
        fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
        fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![]
        }
    }

    fn test_instance() -> (PublicEcdsaInstance<M31>, [M31; DIGEST_BYTES]) {
        let z = P256M31BigInt::from_u256(&U256::from_le_u64s(&[
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            0xA5A5_5A5A_F0F0_0F0F,
            0x0000_DEAD_BEEF_1234,
        ]));
        let (bytes, _carries) = z_digest_byte_witness(&z);
        let digest_bytes = core::array::from_fn(|i| M31::from_u32_unchecked(u32::from(bytes[i])));
        let instance = PublicEcdsaInstance {
            sig_id: M31::from_u32_unchecked(1),
            z,
            r: P256M31BigInt::zero(),
            s: P256M31BigInt::zero(),
            pub_x: P256M31BigInt::zero(),
            pub_y: P256M31BigInt::zero(),
        };
        (instance, digest_bytes)
    }

    fn providers(
        instance: &PublicEcdsaInstance<M31>,
        digest_bytes: [M31; DIGEST_BYTES],
        scalar_z_handle: SharedScalarZRelation,
        digest_handle: SharedRelation<DigestBytesRelation>,
    ) -> AnalyticProviders {
        AnalyticProviders {
            instances: vec![instance.clone()],
            digest_bytes,
            scalar_z_handle,
            digest_handle,
            scalar_z: None,
            digest: None,
        }
    }

    /// The bridge module proves and verifies end-to-end against synthetic
    /// `ScalarZ`/digest providers: a real STARK prove/verify over the shared
    /// orchestrator, validating the layout, commit order, every constraint, and
    /// the global balance in isolation from P256/SHA.
    #[test]
    fn bridge_module_proves_and_verifies() {
        let (instance, digest_bytes) = test_instance();
        let rows = vec![DigestBindRow {
            sig_id: instance.sig_id,
            z: instance.z.clone(),
        }];
        let log_size = 4;

        let scalar_z_handle = SharedScalarZRelation::new();
        let digest_handle = SharedRelation::<DigestBytesRelation>::default();
        let mut provider = providers(
            &instance,
            digest_bytes,
            scalar_z_handle.clone(),
            digest_handle.clone(),
        );
        let mut bridge = DigestBindProver::new(rows, log_size, scalar_z_handle, digest_handle);
        let config = PcsConfig::default();
        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut bridge];
            air_core::prove(&mut modules, config).expect("bridge module proves")
        };
        let claim = bridge.interaction_claim().clone();

        // Verify with fresh handles (the provider re-draws and re-populates them).
        let scalar_z_handle_v = SharedScalarZRelation::new();
        let digest_handle_v = SharedRelation::<DigestBytesRelation>::default();
        let mut provider_v = providers(
            &instance,
            digest_bytes,
            scalar_z_handle_v.clone(),
            digest_handle_v.clone(),
        );
        let mut bridge_v =
            DigestBindVerifier::new(log_size, claim, scalar_z_handle_v, digest_handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut bridge_v];
        air_core::verify(&mut modules, &proof).expect("bridge module verifies");
    }

    /// A digest provider yielding a one-bit-flipped digest breaks the global
    /// balance — the verifier rejects. This is the binding the bridge exists for,
    /// now exercised through a real proof.
    #[test]
    fn bridge_module_rejects_mismatched_digest() {
        let (instance, mut digest_bytes) = test_instance();
        let rows = vec![DigestBindRow {
            sig_id: instance.sig_id,
            z: instance.z.clone(),
        }];
        let log_size = 4;

        // Prover (bridge) uses the honest z; the synthetic digest provider yields
        // a different digest. The verifier's provider matches the prover's
        // (mismatched) one, so the only thing broken is the balance.
        let scalar_z_handle = SharedScalarZRelation::new();
        let digest_handle = SharedRelation::<DigestBytesRelation>::default();
        digest_bytes[0] = M31::from_u32_unchecked(digest_bytes[0].0 ^ 1);
        let mut provider = providers(
            &instance,
            digest_bytes,
            scalar_z_handle.clone(),
            digest_handle.clone(),
        );
        let mut bridge = DigestBindProver::new(rows, log_size, scalar_z_handle, digest_handle);
        let config = PcsConfig::default();
        let proof = {
            let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut bridge];
            air_core::prove(&mut modules, config).expect("prove still succeeds")
        };
        let claim = bridge.interaction_claim().clone();

        let scalar_z_handle_v = SharedScalarZRelation::new();
        let digest_handle_v = SharedRelation::<DigestBytesRelation>::default();
        let mut provider_v = providers(
            &instance,
            digest_bytes,
            scalar_z_handle_v.clone(),
            digest_handle_v.clone(),
        );
        let mut bridge_v =
            DigestBindVerifier::new(log_size, claim, scalar_z_handle_v, digest_handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut bridge_v];
        assert!(
            air_core::verify(&mut modules, &proof).is_err(),
            "a mismatched digest must fail the global balance",
        );
    }
}
