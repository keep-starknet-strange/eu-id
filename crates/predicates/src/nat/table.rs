use crate::nat::types::{PublicInput, PublicInputKind};
use crate::types::Column;
use crate::utils::random_m31_cell;
use air_core::claim_mask::{add_claim_mask_fraction, CLAIM_MASK_MIN_LOG_SIZE};
use num_traits::{One, Zero};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::Column as _;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};

relation!(NatTableElements, 1);

/// Base of the reserved Class-D dummy keys for the accepted-set table. Every
/// valid nationality code — ISO-numeric (`≤ 999`) or alpha-2 packed
/// (`256·b0 + b1 ≤ 256·90 + 90 = 23130`) — is far below this, so the dummy keys
/// are UNREACHABLE by any honest membership use. `dummy_key(i) = base + i`.
const NAT_DUMMY_KEY_BASE: u32 = 1 << 24;

/// Preprocessed accepted-set table id. It encodes both the code space (`kind`)
/// and the exact accepted codes, so a preprocessed column with this id is the
/// same fixed table for every module that shares it — the dedup/fingerprint
/// guard rejects any two modules that reuse the id with different content.
///
/// This is the Class-D **blinded** value column id (real codes in the reachable
/// prefix, reserved dummy keys in the suffix); namespaced with `blind/` so it
/// never aliases a non-blinded table of the same accepted set.
pub fn acceptable_col_id(public: &PublicInput) -> PreProcessedColumnId {
    let kind = match public.kind {
        PublicInputKind::IsoNumeric => "iso",
        PublicInputKind::Alpha2 => "alpha2",
    };
    let ids: Vec<String> = public.acceptable.iter().map(|c| c.to_string()).collect();
    PreProcessedColumnId {
        id: format!("nat/acceptable/blind/{kind}/{}", ids.join(",")),
    }
}

/// Preprocessed `is_dummy` selector id for the blinded accepted-set table: `1`
/// over the reserved dummy suffix, `0` over the reachable prefix.
pub fn acceptable_dummy_col_id(public: &PublicInput) -> PreProcessedColumnId {
    let kind = match public.kind {
        PublicInputKind::IsoNumeric => "iso",
        PublicInputKind::Alpha2 => "alpha2",
    };
    let ids: Vec<String> = public.acceptable.iter().map(|c| c.to_string()).collect();
    PreProcessedColumnId {
        id: format!("nat/acceptable/dummy/{kind}/{}", ids.join(",")),
    }
}

/// Committed row count of the Class-D blinded table, extended to the minimum
/// claim-mask domain when the accepted set is small.
pub fn blind_log_size(public: &PublicInput) -> u32 {
    (public.log_size() + 1).max(CLAIM_MASK_MIN_LOG_SIZE)
}

/// Class-D blinded value column: accepted codes (then zero padding) occupy the
/// reachable prefix `[0, 2^log_size)`; every remaining row carries a reserved
/// dummy key starting at `NAT_DUMMY_KEY_BASE`.
pub fn acceptable_value_column(public: &PublicInput) -> Column {
    let log_size = public.log_size();
    let real = 1usize << log_size;
    let total = 1usize << blind_log_size(public);
    let domain = CanonicCoset::new(blind_log_size(public)).circle_domain();
    let mut col = BaseColumn::zeros(total);
    for (i, &code) in public.acceptable.iter().enumerate() {
        col.set(i, M31::from_u32_unchecked(code));
    }
    // Reachable padding rows stay 0 (no valid code is 0). The suffix contains
    // reserved, unreachable dummy keys.
    for i in 0..total - real {
        col.set(
            real + i,
            M31::from_u32_unchecked(NAT_DUMMY_KEY_BASE + i as u32),
        );
    }
    CircleEvaluation::new(domain, col)
}

/// Class-D `is_dummy` selector: `0` over the reachable prefix and `1` over the
/// dummy suffix.
pub fn acceptable_dummy_column(public: &PublicInput) -> Column {
    let log_size = public.log_size();
    let real = 1usize << log_size;
    let total = 1usize << blind_log_size(public);
    let domain = CanonicCoset::new(blind_log_size(public)).circle_domain();
    let mut col = BaseColumn::zeros(total);
    for i in real..total {
        col.set(i, M31::one());
    }
    CircleEvaluation::new(domain, col)
}

/// Class-D blinded multiplicity column: the number of marked signed entries on
/// each accepted-code row, zero on unused real rows, and fresh random cells on
/// the dummy suffix.
pub fn gen_blind_multiplicity_column(public: &PublicInput, used_rows: &[usize]) -> Column {
    let log_size = public.log_size();
    let real = 1usize << log_size;
    let size = 1usize << blind_log_size(public);
    let mut data = vec![M31::zero(); size];
    for &used_row in used_rows {
        data[used_row] += M31::one();
    }
    for slot in data.iter_mut().take(size).skip(real) {
        *slot = random_m31_cell();
    }
    CircleEvaluation::new(
        CanonicCoset::new(blind_log_size(public)).circle_domain(),
        BaseColumn::from_iter(data),
    )
}

/// Class-D multiplicity-blinded accepted-set table provider (Q-015 §4b).
///
/// Reads the blinded value column (accepted codes in the reachable prefix,
/// reserved dummy keys in the suffix) and the `is_dummy` selector, then emits ONE
/// gated entry per row against the shared relation and the same value: numerator
/// `-(1 − is_dummy) · multiplicity`.
///
/// On a real row (`is_dummy = 0`) the numerator is `-multiplicity` — exactly the
/// unblinded table. On a dummy row it is identically `0` for ANY random `m`, so
/// the blind multiplicities never touch the global balance while staying in the
/// committed multiplicity column as the mask. The dummy keys are unreachable by
/// honest membership uses (every valid code is `< 2^24`), so no consumer can be
/// serviced by a dummy row; `is_dummy` is preprocessed (trusted), so a malicious
/// prover cannot un-gate a dummy row, and both key and gate come from
/// committed/preprocessed data, so there is no free term.
/// `(1 − is_dummy) · multiplicity` is preprocessed × trace = degree 2, within `D ≤ 3`.
#[derive(Clone)]
pub struct NatTableEval {
    pub public: PublicInput,
    pub lookup_elements: NatTableElements,
    pub claim_mask_beta: Option<QM31>,
}

pub type NatTableComponent = FrameworkComponent<NatTableEval>;

impl FrameworkEval for NatTableEval {
    fn log_size(&self) -> u32 {
        blind_log_size(&self.public)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let acc_nat_code = eval.get_preprocessed_column(acceptable_col_id(&self.public));
        let is_dummy = eval.get_preprocessed_column(acceptable_dummy_col_id(&self.public));
        let mult = eval.next_trace_mask();
        // Single gated membership yield `-(1 − is_dummy)·mult`: `-m` on real rows
        // (is_dummy = 0), identically `0` on dummy rows for any committed `m`.
        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from((one - is_dummy) * mult),
            std::slice::from_ref(&acc_nat_code),
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup();
        eval
    }
}

#[cfg(test)]
mod class_d_tests {
    use super::*;

    fn public() -> PublicInput {
        PublicInput::new(vec![276, 250, 300])
    }

    /// Class-D: the blinded value column doubles the domain, keeps the real
    /// accepted codes on the lower half, and reserves unreachable dummy keys on
    /// the upper half; `is_dummy` selects exactly the upper half.
    #[test]
    fn blinded_table_reserves_unreachable_dummy_keys() {
        let public = public();
        let real = 1usize << public.log_size();
        let value = acceptable_value_column(&public);
        let dummy = acceptable_dummy_column(&public);

        assert_eq!(value.domain.log_size(), blind_log_size(&public));
        // Every valid nationality code is far below NAT_DUMMY_KEY_BASE, so no
        // honest membership use can ever land on a dummy key.
        for i in 0..real {
            assert_eq!(dummy.values.at(i).0, 0, "real row {i} must not be a dummy");
        }
        for i in real..1 << blind_log_size(&public) {
            assert_eq!(dummy.values.at(i).0, 1, "dummy row must be selected");
            assert!(
                value.values.at(i).0 >= NAT_DUMMY_KEY_BASE,
                "dummy key must be unreachable (>= NAT_DUMMY_KEY_BASE)"
            );
        }
        assert!(blind_log_size(&public) >= CLAIM_MASK_MIN_LOG_SIZE);
    }

    /// Class-D: the random dummy multiplicities live only in the upper half; the
    /// real code's row carries the count `1`, and each generation reseeds the
    /// dummy cells so the committed column masks the real counts.
    #[test]
    fn blinded_multiplicity_masks_real_counts_with_fresh_dummies() {
        let public = public();
        let real = 1usize << public.log_size();
        let used_row = 1usize; // 276 sits at sorted index 1

        let first = gen_blind_multiplicity_column(&public, &[used_row]);
        let second = gen_blind_multiplicity_column(&public, &[used_row]);
        assert_eq!(
            first.values.at(used_row).0,
            1,
            "the used code's real count is 1"
        );
        // The upper (dummy) half is fresh randomness that differs across runs.
        let upper_first: Vec<u32> = (real..1 << blind_log_size(&public))
            .map(|i| first.values.at(i).0)
            .collect();
        let upper_second: Vec<u32> = (real..1 << blind_log_size(&public))
            .map(|i| second.values.at(i).0)
            .collect();
        assert_ne!(
            upper_first, upper_second,
            "dummy multiplicities must be fresh per generation"
        );
    }
}
