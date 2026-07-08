//! LogUp relation contracts for `sampleinball_fsm` (M5, [CHAL]).
//!
//! Cross-component bindings ([`CCellRelation`], [`HashIoRelation`]) live in
//! [`crate::binding`]; this module adds the FSM's own range tables and the
//! offline-memory-checking channel that pins the Fisher–Yates array swaps.
//!
//! | relation | arity | tuple | provider | consumer |
//! |----------|-------|-------|----------|----------|
//! | `CCell` | 2 | `(c_bind_id, c)` | coeffs C rows (−1) | sampleinball final reads (+1) |
//! | `HashIo`| 3 | `(stream_id, byte_pos, byte)` | sponge/M6 (+1) | FSM stream consume (−1) |
//! | `Mem`   | 3 | `(addr, value, timestamp)` | writes (+) | reads (−) | offline memory |
//! | `Swap`  | 2 | `(step, addr)` | accept rows ×2 (+) | read + write-j rows (−) | FSM↔mem addr tie |
//! | `StepVal`| 2 | `(step, value)` | read rows (+) | write-i rows (−) | FSM↔mem value tie |
//! | `SignBit`| 2 | `(bit_idx, ±1)` | sign rows per bit (+) | write-j rows (−) | FSM↔mem sign tie |
//! | `Rc8`   | 1 | `v ∈ [0,2^8)` | rc8 table | index/byte bounds, sorted daddr |
//! | `Rc9`   | 1 | `v ∈ [0,2^9)` | rc9 table | ternary `{0,1,2}` membership |
//! | `Rc11`  | 1 | `v ∈ [0,2^11)` | rc11 table | offline-memory timestamp diff `dts` |
//!
//! ## Offline memory checking (the swap soundness core)
//!
//! SampleInBall mutates `c[0..N]` via τ steps `c[i_t] = c[j_t]; c[j_t] = s_t`
//! with `i_t = N−τ+t`. We prove the committed final `c` equals applying these
//! writes to a zero array using a read/write-set argument over the `Mem`
//! channel keyed by `(addr, value, timestamp)`:
//! - **init**: write every `(k, 0, ts=0)` (N writes, +).
//! - **each step** reads `(j_t, old, ts_read)` (−) then writes `(i_t, old, ts_a)`
//!   and `(j_t, s_t, ts_b)` (+); the read's value/ts must match the last prior
//!   write to that address (enforced by the balance + a monotone timestamp).
//! - **final**: read every `(k, c[k], ts_final)` (−) — these `c[k]` are exactly
//!   the coeffs-bound values.
//!
//! The multiset of writes (last-writer-wins by timestamp) balances the reads iff
//! the committed `c` is the true SampleInBall output (standard offline-memory
//! soundness; timestamps drawn as an order challenge keep it collision-free).

use stwo_constraint_framework::relation;

use crate::binding::{CCellRelation, HashIoRelation};

/// `(addr, value, timestamp)` offline-memory channel.
pub const MEM_ARITY: usize = 3;
relation!(MemRelation, MEM_ARITY);

// Arity-1 range table relation (independent instances).
relation!(RcRelation, 1);

/// Arity-2 FSM↔memory tie channels. These close the free-witness hole in the
/// core access list: without them the unsorted `(u_addr, u_val, u_ts, u_write)`
/// columns are unconstrained (only `u_write` booleanity + the Mem yield), so a
/// prover could commit an arbitrary memory-consistent history and the swap-replay
/// gate would be vacuous. The three channels bind every core access back to the
/// FSM rows (accepted byte, read value, FIPS sign bit):
///
/// | relation  | arity | tuple                         | provider (+)              | consumer (−)                 |
/// |-----------|-------|-------------------------------|---------------------------|------------------------------|
/// | `Swap`    | 2     | `(step_ordinal, address)`     | accept rows ×2 `(t, byte)`| read + write-j rows `(t, addr)` |
/// | `StepVal` | 2     | `(step_ordinal, value)`       | read rows `(t, read_val)` | write-i rows `(t, wr_i_val)` |
/// | `SignBit` | 2     | `(sign_bit_index, ±1 value)`  | sign rows per bit `(8b+u, 1−2·bit)` | write-j rows `(t, wr_j_val)` |
pub const SWAP_ARITY: usize = 2;
pub const STEPVAL_ARITY: usize = 2;
pub const SIGNBIT_ARITY: usize = 2;
relation!(SwapRelation, SWAP_ARITY);
relation!(StepValRelation, STEPVAL_ARITY);
relation!(SignBitRelation, SIGNBIT_ARITY);

#[derive(Clone)]
pub struct SibRelations {
    pub ccell: CCellRelation,
    pub hash_io: HashIoRelation,
    pub mem: MemRelation,
    pub swap: SwapRelation,
    pub stepval: StepValRelation,
    pub signbit: SignBitRelation,
    pub rc8: RcRelation,
    pub rc9: RcRelation,
    pub rc11: RcRelation,
}

impl SibRelations {
    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            ccell: CCellRelation::draw(channel),
            hash_io: HashIoRelation::draw(channel),
            mem: MemRelation::draw(channel),
            swap: SwapRelation::draw(channel),
            stepval: StepValRelation::draw(channel),
            signbit: SignBitRelation::draw(channel),
            rc8: RcRelation::draw(channel),
            rc9: RcRelation::draw(channel),
            rc11: RcRelation::draw(channel),
        }
    }

    /// Composed-statement constructor (M6): draw only the sib-private relations
    /// (mem + range tables) and reuse SHARED `ccell` (from coeffs) and `hash_io`
    /// (from the SIB-chain sponge) instances so the c-binding and squeeze-stream
    /// bytes cancel across components. Private draw order matches [`Self::draw`].
    pub fn draw_with(
        channel: &mut impl stwo::core::channel::Channel,
        ccell: CCellRelation,
        hash_io: HashIoRelation,
    ) -> Self {
        Self {
            ccell,
            hash_io,
            mem: MemRelation::draw(channel),
            swap: SwapRelation::draw(channel),
            stepval: StepValRelation::draw(channel),
            signbit: SignBitRelation::draw(channel),
            rc8: RcRelation::draw(channel),
            rc9: RcRelation::draw(channel),
            rc11: RcRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            ccell: CCellRelation::dummy(),
            hash_io: HashIoRelation::dummy(),
            mem: MemRelation::dummy(),
            swap: SwapRelation::dummy(),
            stepval: StepValRelation::dummy(),
            signbit: SignBitRelation::dummy(),
            rc8: RcRelation::dummy(),
            rc9: RcRelation::dummy(),
            rc11: RcRelation::dummy(),
        }
    }
}
