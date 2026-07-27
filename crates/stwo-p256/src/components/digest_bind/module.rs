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
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use crate::range_checks::component::BlindRangeCheckEval;
use crate::range_checks::{
    ColumnEval, RangeCheckClaim, RangeCheckInteractionClaim, RangeCheckRelation,
};

use super::air::{active_col_id, digest_bind_lookups, DigestBindComponent, DigestBindEval};
use super::witness::{
    active_preprocessed_column, gen_base_trace, gen_interaction_trace, range_uses,
    DigestBindRelations, DigestBindRow,
};
use super::{ScalarZRelation, SharedScalarZRelation, TOTAL_COLS};
use air_core::relations::SharedRelation;

const EXT: usize = SECURE_EXTENSION_DEGREE;

/// Fresh uniform M31 cell from the host CSPRNG (never channel-derived: the
/// Class-D blind multiplicities must stay secret from the verifier).
/// Rejection-sampled like the per-module `random_m31` helpers elsewhere.
fn random_m31() -> stwo::core::fields::m31::M31 {
    use rand::RngCore;
    let mut rng = rand::thread_rng();
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate != 0x7fff_ffff {
            return stwo::core::fields::m31::M31::from_u32_unchecked(candidate);
        }
    }
}

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
/// Class-D `is_dummy` selector ids for the two namespaced bridge range tables.
fn byte_range_dummy_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "digest_bind_byte_range_dummy".to_string(),
    }
}
fn carry_range_dummy_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "digest_bind_carry_range_dummy".to_string(),
    }
}

/// Build a Class-D blinded range provider ([`BlindRangeCheckEval`]) reading the
/// bridge's **namespaced** value/is_dummy preprocessed ids, so the bridge's
/// tables neither alias P256's generic `p256_range{k}_*` ids nor leak their
/// per-key multiplicities. The committed domain is `real_bits + 1`.
fn namespaced_blind_eval(
    relation: RangeCheckRelation,
    real_bits: u32,
    value_id: PreProcessedColumnId,
    dummy_id: PreProcessedColumnId,
) -> BlindRangeCheckEval {
    BlindRangeCheckEval {
        relation,
        real_log_size: real_bits,
        value_id,
        dummy_id,
    }
}

type NamespacedRangeComponent = FrameworkComponent<BlindRangeCheckEval>;

/// Number of base-field interaction columns produced by `n_lookups` lookups
/// under paired batching (`finalize_logup_in_pairs`): `ceil(n / 2)` secure
/// columns × `SECURE_EXTENSION_DEGREE`.
fn interaction_base_cols(n_lookups: usize) -> usize {
    n_lookups.div_ceil(2) * EXT
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

/// Class-D committed width of a bridge range table: one log above the real
/// width (upper half = reserved dummy-key blind region).
const BYTE_RANGE_BLIND_BITS: u32 = BYTE_RANGE_BITS + 1;
const CARRY_RANGE_BLIND_BITS: u32 = CARRY_RANGE_BITS + 1;

fn layout(log_size: u32) -> TreeLayout {
    // Preprocessed: digest_bind active selector, then per range table a value
    // column and a Class-D is_dummy selector, each at the blinded log size.
    let preprocessed = vec![
        log_size,
        BYTE_RANGE_BLIND_BITS,
        BYTE_RANGE_BLIND_BITS,
        CARRY_RANGE_BLIND_BITS,
        CARRY_RANGE_BLIND_BITS,
    ];
    // Trace: digest_bind's witness columns at `log_size`, then one multiplicity
    // column per range table at the table's blinded log size.
    let mut trace = vec![log_size; TOTAL_COLS];
    trace.push(BYTE_RANGE_BLIND_BITS);
    trace.push(CARRY_RANGE_BLIND_BITS);
    // Interaction: digest_bind's paired logup columns at `log_size`, then one
    // logup column per range table. The Class-D provider emits TWO fractions
    // per row (`-mult` and `+is_dummy·mult`), paired into ONE column.
    let mut interaction = vec![log_size; interaction_base_cols(digest_bind_lookups(true))];
    interaction.extend(std::iter::repeat_n(
        BYTE_RANGE_BLIND_BITS,
        interaction_base_cols(2),
    ));
    interaction.extend(std::iter::repeat_n(
        CARRY_RANGE_BLIND_BITS,
        interaction_base_cols(2),
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
        active_rows: usize,
        relations: &DrawnRelations,
        scalar_z: ScalarZRelation,
        digest: DigestBytesRelation,
        claim: &DigestBindInteractionClaim,
    ) -> Self {
        let digest_bind = DigestBindComponent::new(
            allocator,
            DigestBindEval {
                log_size,
                active_rows,
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
            namespaced_blind_eval(
                relations.byte_range.clone(),
                BYTE_RANGE_BITS,
                byte_range_value_id(),
                byte_range_dummy_id(),
            ),
            claim.byte_range,
        );
        let carry_range = NamespacedRangeComponent::new(
            allocator,
            namespaced_blind_eval(
                relations.carry_range.clone(),
                CARRY_RANGE_BITS,
                carry_range_value_id(),
                carry_range_dummy_id(),
            ),
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

fn preprocessed_ids(log_size: u32, active_rows: usize) -> Vec<PreProcessedColumnId> {
    vec![
        active_col_id(log_size, active_rows),
        byte_range_value_id(),
        byte_range_dummy_id(),
        carry_range_value_id(),
        carry_range_dummy_id(),
    ]
}

/// Prover-side bridge module.
pub struct DigestBindProver {
    rows: Vec<DigestBindRow>,
    log_size: u32,
    active_rows: usize,
    scalar_z_handle: SharedScalarZRelation,
    digest_handle: SharedRelation<DigestBytesRelation>,
    relations: Option<DrawnRelations>,
    interaction_claim: Option<DigestBindInteractionClaim>,
    components: Option<DigestBindComponents>,
    /// Class-D blinded multiplicity columns, generated once in `write_trace`
    /// (random upper half sampled fresh) and reused in `write_interaction` so
    /// the committed trace and the interaction fractions agree exactly.
    byte_mult: Option<ColumnEval>,
    carry_mult: Option<ColumnEval>,
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
            active_rows: rows.len(),
            rows,
            log_size,
            scalar_z_handle,
            digest_handle,
            relations: None,
            interaction_claim: None,
            components: None,
            byte_mult: None,
            carry_mult: None,
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
        channel.mix_u64(self.active_rows as u64);
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
        preprocessed_ids(self.log_size, self.active_rows)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        self.components = Some(DigestBindComponents::build(
            allocator,
            self.log_size,
            self.active_rows,
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
        // The Class-D blinded carry range table (`2^14`) is the largest
        // committed domain.
        CARRY_RANGE_BLIND_BITS.max(self.log_size)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // digest_bind is degree 2; each Class-D range provider is degree 2
        // (`is_dummy · mult`) at its blinded `log_size + 1`. The blinded carry
        // table's bound (`14 + 1`) dominates.
        (self.log_size + 1)
            .max(BYTE_RANGE_BLIND_BITS + 1)
            .max(CARRY_RANGE_BLIND_BITS + 1)
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let ids = preprocessed_ids(self.log_size, self.active_rows);
        self.write_selected_preprocessed(tb, &ids);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let byte_claim = RangeCheckClaim::new(BYTE_RANGE_BITS);
        let carry_claim = RangeCheckClaim::new(CARRY_RANGE_BITS);
        let columns = vec![
            active_preprocessed_column(self.log_size, self.active_rows),
            byte_claim.gen_blind_preprocessed_column(),
            byte_claim.gen_blind_dummy_column(),
            carry_claim.gen_blind_preprocessed_column(),
            carry_claim.gen_blind_dummy_column(),
        ];
        fingerprint_preprocessed_columns(
            "stwo_p256::DigestBindProver",
            &preprocessed_ids(self.log_size, self.active_rows),
            &columns,
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let active = active_preprocessed_column(self.log_size, self.active_rows);
        let byte_claim = RangeCheckClaim::new(BYTE_RANGE_BITS);
        let carry_claim = RangeCheckClaim::new(CARRY_RANGE_BITS);
        let ids = preprocessed_ids(self.log_size, self.active_rows);
        let columns = vec![
            active,
            byte_claim.gen_blind_preprocessed_column(),
            byte_claim.gen_blind_dummy_column(),
            carry_claim.gen_blind_preprocessed_column(),
            carry_claim.gen_blind_dummy_column(),
        ];
        if selected_ids == ids.as_slice() {
            tb.extend_evals(columns);
            return;
        }
        let selected = selected_ids
            .iter()
            .map(|selected_id| {
                ids.iter()
                    .zip(&columns)
                    .find_map(|(id, column)| (id == selected_id).then(|| column.clone()))
                    .unwrap_or_else(|| {
                        panic!(
                            "selected preprocessed column {} is not owned by this digest bridge",
                            selected_id.id
                        )
                    })
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut cols: Vec<ColumnEval> = gen_base_trace(&self.rows, self.log_size);
        let (byte_uses, carry_uses) = range_uses(&self.rows);
        // Class-D blinded multiplicity columns: real counts on the lower half,
        // fresh host-CSPRNG randomness on the reserved dummy upper half. Cache
        // them so `write_interaction` folds the SAME cells.
        let byte_mult = RangeCheckClaim::new(BYTE_RANGE_BITS)
            .gen_blind_multiplicity_trace(byte_uses, random_m31);
        let carry_mult = RangeCheckClaim::new(CARRY_RANGE_BITS)
            .gen_blind_multiplicity_trace(carry_uses, random_m31);
        cols.push(byte_mult.clone());
        cols.push(carry_mult.clone());
        self.byte_mult = Some(byte_mult);
        self.carry_mult = Some(carry_mult);
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
        let active = active_preprocessed_column(self.log_size, self.active_rows);
        let (digest_bind_cols, digest_bind_sum) =
            gen_interaction_trace(&active, &base, &bridge_relations, true);

        let byte_claim_gen = RangeCheckClaim::new(BYTE_RANGE_BITS);
        let byte_value = byte_claim_gen.gen_blind_preprocessed_column();
        let byte_dummy = byte_claim_gen.gen_blind_dummy_column();
        let byte_mult = self
            .byte_mult
            .as_ref()
            .expect("byte multiplicity is generated in write_trace");
        let (byte_cols, byte_claim) = RangeCheckInteractionClaim::gen_blind_interaction_trace(
            byte_mult,
            &byte_value,
            &byte_dummy,
            &relations.byte_range,
        );
        let carry_claim_gen = RangeCheckClaim::new(CARRY_RANGE_BITS);
        let carry_value = carry_claim_gen.gen_blind_preprocessed_column();
        let carry_dummy = carry_claim_gen.gen_blind_dummy_column();
        let carry_mult = self
            .carry_mult
            .as_ref()
            .expect("carry multiplicity is generated in write_trace");
        let (carry_cols, carry_claim) = RangeCheckInteractionClaim::gen_blind_interaction_trace(
            carry_mult,
            &carry_value,
            &carry_dummy,
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
    active_rows: usize,
    scalar_z_handle: SharedScalarZRelation,
    digest_handle: SharedRelation<DigestBytesRelation>,
    interaction_claim: DigestBindInteractionClaim,
    relations: Option<DrawnRelations>,
    components: Option<DigestBindComponents>,
}

impl DigestBindVerifier {
    pub fn new(
        log_size: u32,
        active_rows: usize,
        interaction_claim: DigestBindInteractionClaim,
        scalar_z_handle: SharedScalarZRelation,
        digest_handle: SharedRelation<DigestBytesRelation>,
    ) -> Self {
        Self {
            log_size,
            active_rows,
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
        channel.mix_u64(self.active_rows as u64);
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
        preprocessed_ids(self.log_size, self.active_rows)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(DigestBindComponents::build(
            allocator,
            self.log_size,
            self.active_rows,
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
    fn bridge_layout_puts_active_selector_in_preprocessed_tree() {
        let log_size = 9;
        let bridge_layout = layout(log_size);

        assert_eq!(
            bridge_layout.preprocessed.first(),
            Some(&log_size),
            "digest bridge active selector must be preprocessed at bridge log size"
        );
    }

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
            DigestBindVerifier::new(log_size, 1, claim, scalar_z_handle_v, digest_handle_v);
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
            DigestBindVerifier::new(log_size, 1, claim, scalar_z_handle_v, digest_handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut bridge_v];
        assert!(
            air_core::verify(&mut modules, &proof).is_err(),
            "a mismatched digest must fail the global balance",
        );
    }

    // ---- Class D (Q-015 §4b / p4c) bridge range-table blinding ----

    /// The bridge's Class-D range tables commit at one log above their real
    /// width, and the reserved dummy region is exactly the upper half.
    #[test]
    fn class_d_bridge_range_tables_use_doubled_domain() {
        assert_eq!(BYTE_RANGE_BLIND_BITS, BYTE_RANGE_BITS + 1);
        assert_eq!(CARRY_RANGE_BLIND_BITS, CARRY_RANGE_BITS + 1);
        let byte = RangeCheckClaim::new(BYTE_RANGE_BITS);
        assert_eq!(byte.blind_log_size(), BYTE_RANGE_BITS + 1);
        let dummy = byte.gen_blind_dummy_column();
        assert_eq!(dummy.domain.log_size(), BYTE_RANGE_BITS + 1);
        // Lower half real (is_dummy = 0), upper half reserved (is_dummy = 1).
        let ones = dummy
            .data
            .iter()
            .flat_map(|packed| packed.to_array())
            .filter(|v| v.0 == 1)
            .count();
        assert_eq!(
            ones,
            1usize << BYTE_RANGE_BITS,
            "exactly the upper half is the reserved dummy region",
        );
    }

    /// Prove the bridge twice for the same witness: the dummy-region blind
    /// multiplicity cells differ across proofs (fresh host randomness) and both
    /// proofs verify. Proves the Class-D masking is per-proof non-deterministic
    /// without disturbing correctness.
    #[test]
    fn class_d_bridge_dummy_multiplicities_are_fresh_and_both_verify() {
        let (instance, digest_bytes) = test_instance();
        let make_rows = || {
            vec![DigestBindRow {
                sig_id: instance.sig_id,
                z: instance.z.clone(),
            }]
        };
        let log_size = 4;

        let prove_once = || {
            let scalar_z_handle = SharedScalarZRelation::new();
            let digest_handle = SharedRelation::<DigestBytesRelation>::default();
            let mut provider = providers(
                &instance,
                digest_bytes,
                scalar_z_handle.clone(),
                digest_handle.clone(),
            );
            let mut bridge =
                DigestBindProver::new(make_rows(), log_size, scalar_z_handle, digest_handle);
            let config = PcsConfig::default();
            let proof = {
                let mut modules: [&mut dyn AirProver; 2] = [&mut provider, &mut bridge];
                air_core::prove(&mut modules, config).expect("bridge Class-D proves")
            };
            // The dummy region is the upper half of the blinded byte-mult column.
            let byte_mult = bridge.byte_mult.clone().expect("byte mult cached");
            let cells: Vec<u32> = byte_mult
                .data
                .iter()
                .flat_map(|packed| packed.to_array())
                .map(|v| v.0)
                .collect();
            let real = 1usize << BYTE_RANGE_BITS;
            let dummy_cells: Vec<u32> = cells[real..].to_vec();
            (proof, bridge.interaction_claim().clone(), dummy_cells)
        };

        let (proof_a, claim_a, dummy_a) = prove_once();
        let (proof_b, claim_b, dummy_b) = prove_once();

        assert_ne!(
            dummy_a, dummy_b,
            "Class-D dummy-region multiplicity cells must be fresh per proof",
        );

        // Both proofs verify.
        for (proof, claim) in [(&proof_a, &claim_a), (&proof_b, &claim_b)] {
            let scalar_z_handle_v = SharedScalarZRelation::new();
            let digest_handle_v = SharedRelation::<DigestBytesRelation>::default();
            let mut provider_v = providers(
                &instance,
                digest_bytes,
                scalar_z_handle_v.clone(),
                digest_handle_v.clone(),
            );
            let mut bridge_v = DigestBindVerifier::new(
                log_size,
                1,
                claim.clone(),
                scalar_z_handle_v,
                digest_handle_v,
            );
            let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut bridge_v];
            air_core::verify(&mut modules, proof).expect("Class-D proof verifies");
        }
    }

    /// Tampering a blinded range table's published claimed sum (the
    /// cancelling-pair term's net) breaks the component's LogUp boundary at
    /// OODS, so verification fails. Proves the dummy-region blinding is bound,
    /// not a free term.
    #[test]
    fn class_d_bridge_balance_tamper_rejected() {
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
            air_core::prove(&mut modules, config).expect("bridge Class-D proves")
        };
        let mut claim = bridge.interaction_claim().clone();
        // Tamper the blinded byte-range table's published claimed sum.
        claim.byte_range += SecureField::from(M31::from_u32_unchecked(1));

        let scalar_z_handle_v = SharedScalarZRelation::new();
        let digest_handle_v = SharedRelation::<DigestBytesRelation>::default();
        let mut provider_v = providers(
            &instance,
            digest_bytes,
            scalar_z_handle_v.clone(),
            digest_handle_v.clone(),
        );
        let mut bridge_v =
            DigestBindVerifier::new(log_size, 1, claim, scalar_z_handle_v, digest_handle_v);
        let mut modules: [&mut dyn Air; 2] = [&mut provider_v, &mut bridge_v];
        assert!(
            air_core::verify(&mut modules, &proof).is_err(),
            "tampering a Class-D claimed sum must be rejected",
        );
    }
}
