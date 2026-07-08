//! LogUp relations for the Keccak / SHAKE-256 AIR.
//!
//! Two families of relations live here:
//!
//! 1. **Interface relations** — [`KeccakStateRelation`] and [`HashIoRelation`].
//!    These are the *only* surface downstream ML-DSA components touch. They are
//!    documented as a frozen cross-module contract below.
//! 2. **Internal table/chain relations** — [`Xor3`], [`AndNot`], [`Conv`], the
//!    seven `Split*` spread byte-split channels, and [`KeccakRound`]. These wire
//!    the three compute components (`sponge` → `keccak` → `keccak_round`) to
//!    their spread-form lookup tables and to each other. Downstream code never
//!    names them.
//!
//! Each `relation!(_, N)` declares a struct wrapping `LookupElements<N>`; `N`
//! is the base-field arity of one lookup tuple. Stwo's macro implements
//! `Relation::combine`, collapsing an `&[F]` of `N` cells into the extension
//! key the interaction column reads.

#![allow(non_camel_case_types)]

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

use crate::constants::{N_BYTES_IN_STATE, N_BYTES_IN_U64};

// ───────────────────────────── Interface relations ─────────────────────────

/// Arity of [`KeccakStateRelation`]: `perm_id`, `direction`, then the 200
/// state limbs (carried in **spread** form; see [`crate::utils`]).
pub const KECCAK_STATE_ARITY: usize = 2 + N_BYTES_IN_STATE;

relation!(KeccakStateRelation, KECCAK_STATE_ARITY);

/// Permutation-chaining relation between the sponge and the permutation prover.
///
/// A tuple is `(perm_id, direction, s_0, s_1, …, s_199)`:
/// - `perm_id` — a running index that uniquely labels one Keccak-f[1600]
///   invocation *within a single proof*. The sponge assigns `perm_id`s
///   densely `0, 1, …` in issue order; the `keccak` permutation prover echoes
///   the same id on both its input- and output-state tuples so the two sides
///   pair up. `perm_id` prevents a malicious prover from satisfying one
///   sponge permute-request with a different request's permutation.
/// - `direction` — `IN` (0) for the pre-permutation state, `OUT` (1) for the
///   post-permutation state. The pair `(perm_id, IN)` / `(perm_id, OUT)`
///   binds one permutation's endpoints.
/// - `s_0..s_199` — the 200 little-endian state limbs (`lane*8 + byte`), each
///   the *spread* of the corresponding state byte. The whole Keccak state stays
///   in spread form across permutations; byte form appears only at the HashIo
///   boundary (see [`crate::sponge`]).
///
/// ## Multiplicity convention
///
/// The **sponge** is the requester: it *yields* (positive multiplicity) one
/// `(perm_id, IN, pre_state)` and requires (negative) one
/// `(perm_id, OUT, post_state)` per permutation it needs. The **keccak**
/// permutation prover is the provider: for each row it *requires* (negative)
/// its `(perm_id, IN, ·)` input and *yields* (positive) its `(perm_id, OUT, ·)`
/// output. The two balance iff every sponge request is served by exactly one
/// proven permutation with matching endpoints. (Signs are symmetric; the fixed
/// convention is what matters — see `interaction.rs` for the concrete signs.)
pub mod direction {
    /// Pre-permutation state tag.
    pub const IN: u32 = 0;
    /// Post-permutation state tag.
    pub const OUT: u32 = 1;
}

/// Arity of [`HashIoRelation`]: `(stream_id, byte_pos, byte)`.
pub const HASH_IO_ARITY: usize = 3;

relation!(HashIoRelation, HASH_IO_ARITY);

/// Byte-stream I/O relation — the contract for feeding message bytes in and
/// reading squeeze bytes out of a SHAKE-256 instance.
///
/// A tuple is `(stream_id, byte_pos, byte)`:
/// - `stream_id` — labels one logical hash stream within a proof. Absorb bytes
///   and squeeze bytes of the same SHAKE instance share a `stream_id` only if
///   they are the same physical byte position of the same direction; callers
///   pick a disjoint id per (instance, in/out) pair as needed.
/// - `byte_pos` — the position of the byte within its stream (0-based).
/// - `byte` — the byte value in `[0, 256)`.
///
/// ## Multiplicity convention
///
/// Keying on `(stream_id, byte_pos)` lets a producer and a consumer pin the
/// same byte without an ordering column: they emit the same first two cells.
/// The direction of yield/require is chosen by the composition:
/// - For **absorb**: the upstream data provider *yields* each declared input
///   byte; the sponge *consumes* it. A byte the sponge actually absorbs that
///   differs from the declared byte breaks the balance (negative test:
///   "absorbed byte differs from HashIo-declared byte → logup imbalance").
/// - For **squeeze**: the sponge *yields* each output byte; a downstream
///   consumer requires it. Reading a wrong squeeze byte breaks the balance.
///
/// The sponge module documents the exact per-side signs it uses.
pub struct HashIoDoc;

// ───────────────────────────── Internal relations ──────────────────────────

/// `xor3` channel: `(key, spread(xor))` with `key = s1+s2+s3` — arity 2, the
/// key being a degree-1 linear combo of committed spread cells.
pub const DENSE_LOOKUP_ARITY: usize = 2;
relation!(Xor3, DENSE_LOOKUP_ARITY);

// `andnot` channel: `(u, spread(¬b'∧b''))` with `u = spread(b')+2·spread(b'')`.
relation!(AndNot, DENSE_LOOKUP_ARITY);

// `conv` byte↔spread channel: `(byte, spread(byte))` — arity 2.
relation!(Conv, DENSE_LOOKUP_ARITY);

/// Spread split channels, one per sub-byte shift `r ∈ {1..=7}`:
/// `(spread_byte, spread_hi, spread_lo)`.
pub const SPLIT_LOOKUP_ARITY: usize = 3;
relation!(Split1, SPLIT_LOOKUP_ARITY);
relation!(Split2, SPLIT_LOOKUP_ARITY);
relation!(Split3, SPLIT_LOOKUP_ARITY);
relation!(Split4, SPLIT_LOOKUP_ARITY);
relation!(Split5, SPLIT_LOOKUP_ARITY);
relation!(Split6, SPLIT_LOOKUP_ARITY);
relation!(Split7, SPLIT_LOOKUP_ARITY);

/// Arity of [`KeccakRound`]: 8 round-constant bytes then the 200 state bytes.
pub const KECCAK_ROUND_ARITY: usize = N_BYTES_IN_U64 + N_BYTES_IN_STATE;
relation!(KeccakRound, KECCAK_ROUND_ARITY);

/// Every relation the Keccak AIR draws, held together so prove and verify draw
/// them from the shared transcript in one deterministic order.
#[derive(Clone, Debug)]
pub struct KeccakRelations {
    pub keccak_state: KeccakStateRelation,
    pub hash_io: HashIoRelation,
    pub keccak_round: KeccakRound,
    pub xor3: Xor3,
    pub andnot: AndNot,
    pub conv: Conv,
    pub split: [SplitRelation; 7],
}

/// A type-erasing wrapper over the seven `Split*` channels so the round
/// component can index them by shift `r-1` without a 7-arm match.
///
/// `relation!` generates seven *distinct* types with identical arity; a slice
/// needs one type. `combine`/`draw` are forwarded so the wrapper behaves like
/// any relation from the framework's perspective.
#[derive(Clone, Debug)]
pub enum SplitRelation {
    S1(Split1),
    S2(Split2),
    S3(Split3),
    S4(Split4),
    S5(Split5),
    S6(Split6),
    S7(Split7),
}

impl<F, EF> stwo_constraint_framework::Relation<F, EF> for SplitRelation
where
    F: Clone,
    EF: stwo_constraint_framework::RelationEFTraitBound<F>,
{
    fn combine(&self, values: &[F]) -> EF {
        match self {
            SplitRelation::S1(r) => r.combine(values),
            SplitRelation::S2(r) => r.combine(values),
            SplitRelation::S3(r) => r.combine(values),
            SplitRelation::S4(r) => r.combine(values),
            SplitRelation::S5(r) => r.combine(values),
            SplitRelation::S6(r) => r.combine(values),
            SplitRelation::S7(r) => r.combine(values),
        }
    }

    fn get_name(&self) -> &str {
        match self {
            SplitRelation::S1(_) => "Split1",
            SplitRelation::S2(_) => "Split2",
            SplitRelation::S3(_) => "Split3",
            SplitRelation::S4(_) => "Split4",
            SplitRelation::S5(_) => "Split5",
            SplitRelation::S6(_) => "Split6",
            SplitRelation::S7(_) => "Split7",
        }
    }

    fn get_size(&self) -> usize {
        SPLIT_LOOKUP_ARITY
    }
}

impl KeccakRelations {
    /// Draw every relation from the shared channel, in a fixed order.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            keccak_state: KeccakStateRelation::draw(channel),
            hash_io: HashIoRelation::draw(channel),
            keccak_round: KeccakRound::draw(channel),
            xor3: Xor3::draw(channel),
            andnot: AndNot::draw(channel),
            conv: Conv::draw(channel),
            split: [
                SplitRelation::S1(Split1::draw(channel)),
                SplitRelation::S2(Split2::draw(channel)),
                SplitRelation::S3(Split3::draw(channel)),
                SplitRelation::S4(Split4::draw(channel)),
                SplitRelation::S5(Split5::draw(channel)),
                SplitRelation::S6(Split6::draw(channel)),
                SplitRelation::S7(Split7::draw(channel)),
            ],
        }
    }

    /// Constant channels for AIR tests without a real transcript (mirrors the
    /// Stwo Blake example's `dummy()` pattern).
    pub fn dummy() -> Self {
        Self {
            keccak_state: KeccakStateRelation::dummy(),
            hash_io: HashIoRelation::dummy(),
            keccak_round: KeccakRound::dummy(),
            xor3: Xor3::dummy(),
            andnot: AndNot::dummy(),
            conv: Conv::dummy(),
            split: [
                SplitRelation::S1(Split1::dummy()),
                SplitRelation::S2(Split2::dummy()),
                SplitRelation::S3(Split3::dummy()),
                SplitRelation::S4(Split4::dummy()),
                SplitRelation::S5(Split5::dummy()),
                SplitRelation::S6(Split6::dummy()),
                SplitRelation::S7(Split7::dummy()),
            ],
        }
    }
}
