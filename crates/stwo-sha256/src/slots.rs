//! Multi-message (slot-scheduled) configuration for the SHA-256 consumer.
//!
//! One merged `Sha256Eval` instance proves `n_slots` independent SHA-256
//! computations, one per fixed **slot region** of `2^slot_log` rows. The
//! schedule is public and preprocessed-pinned: slot `s` occupies rows
//! `[s·2^slot_log, (s+1)·2^slot_log)` of the merged trace, and the AIR gates
//! every per-slot fact (IV reset, digest attribution, field-byte
//! attribution) on preprocessed slot columns whose IDs encode the schedule
//! (I-5). Each slot keeps the single-instance privacy semantics: the
//! message's block count stays witness-private inside the slot's capacity
//! (`< 2^slot_log / 64` blocks — at least one in-slot 64-row padding region,
//! mirroring [`crate::trace::min_log_size`]'s strict bound).
//!
//! Design/audit record: `tasks/sha-multimessage-design.md` (S8).

use crate::field_exposure::FieldExposure;
use crate::trace::ROWS_PER_BLOCK;

/// Per-slot exposure surface — the same knobs a single `Sha256Prover`
/// instance has (`with_digest_handle` / `with_field_handle`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotSpec {
    /// Yield this slot's final-block digest on its own per-slot digest
    /// relation.
    pub expose_digest: bool,
    /// This slot's credential-field byte exposure (its own per-slot field
    /// relation). Empty ⇒ no field columns / yields for the slot.
    pub field_exposure: FieldExposure,
}

/// The public multi-slot schedule + per-slot exposure surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiSlotConfig {
    /// `log2` of every slot region's row count. Uniform slots keep the
    /// preprocessed-ID encoding and the region arithmetic trivial.
    pub slot_log: u32,
    pub slots: Vec<SlotSpec>,
}

impl MultiSlotConfig {
    pub fn new(slot_log: u32, slots: Vec<SlotSpec>) -> Self {
        // A slot must hold at least one whole block plus one in-slot padding
        // block region (the strict `min_log_size` bound, per slot).
        assert!(
            (1usize << slot_log) > ROWS_PER_BLOCK,
            "slot_log {slot_log} cannot hold a block plus in-slot padding"
        );
        assert!(!slots.is_empty(), "multi-slot config needs at least 1 slot");
        Self { slot_log, slots }
    }

    pub fn n_slots(&self) -> usize {
        self.slots.len()
    }

    pub fn slot_rows(&self) -> usize {
        1usize << self.slot_log
    }

    /// Smallest legal `log_n_rows` for this schedule.
    pub fn min_log_n_rows(&self) -> u32 {
        let rows = self.n_slots() * self.slot_rows();
        rows.next_power_of_two().ilog2().max(self.slot_log)
    }

    /// First row of slot `s`.
    pub fn slot_start_row(&self, s: usize) -> usize {
        s * self.slot_rows()
    }

    /// Maximum block count a slot's message may occupy (strictly less than
    /// the capacity, so every slot keeps an in-slot padding region and the
    /// `is_last_block` gate can fire — mirror of `min_log_size`).
    pub fn max_blocks_per_slot(&self) -> usize {
        self.slot_rows() / ROWS_PER_BLOCK - 1
    }

    /// Base column (0-based within the merged dynamic field tail) of slot
    /// `s`'s self-contained field tail. Each slot's tail reuses the
    /// single-instance layout verbatim: byte columns, then (multi-block
    /// exposure only) one block counter and one selector per yield — the
    /// [`FieldExposure`] slot arithmetic applies unchanged at this offset.
    pub fn field_tail_base(&self, s: usize) -> usize {
        self.slots[..s]
            .iter()
            .map(|spec| spec.field_exposure.n_columns())
            .sum()
    }

    /// Total dynamic field-tail width of the merged trace.
    pub fn n_field_columns(&self) -> usize {
        self.field_tail_base(self.n_slots())
    }

    /// Number of slots that yield a digest.
    pub fn n_digest_slots(&self) -> usize {
        self.slots.iter().filter(|s| s.expose_digest).count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec(expose_digest: bool, windows: &[(u32, usize, usize)]) -> SlotSpec {
        SlotSpec {
            expose_digest,
            field_exposure: FieldExposure::from_preimage_windows_multi(windows),
        }
    }

    #[test]
    fn schedule_arithmetic() {
        let config = MultiSlotConfig::new(
            8,
            vec![
                spec(false, &[(7, 0, 20)]),
                spec(true, &[(8, 100, 4)]),
                spec(true, &[]),
            ],
        );
        assert_eq!(config.n_slots(), 3);
        assert_eq!(config.slot_rows(), 256);
        assert_eq!(config.min_log_n_rows(), 10);
        assert_eq!(config.slot_start_row(2), 512);
        assert_eq!(config.max_blocks_per_slot(), 3);
        assert_eq!(config.n_digest_slots(), 2);
        // slot 0: 20 bytes → words 0..5 → 20 byte cols, block-0 legacy (no
        // counter/selectors). slot 1: multi-block (block 1) → 4 byte cols +
        // counter + 4 selectors.
        assert_eq!(config.field_tail_base(0), 0);
        assert_eq!(config.field_tail_base(1), 20);
        assert_eq!(config.field_tail_base(2), 20 + 4 + 1 + 4);
        assert_eq!(config.n_field_columns(), 29);
    }

    #[test]
    #[should_panic(expected = "cannot hold a block")]
    fn rejects_slot_log_without_padding_room() {
        let _ = MultiSlotConfig::new(6, vec![spec(false, &[])]);
    }
}
