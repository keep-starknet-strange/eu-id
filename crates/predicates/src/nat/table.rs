use crate::nat::nationalities::{signed_alpha2_codes, ASSIGNED_ISO_ALPHA2};
use crate::nat::types::PublicInput;
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
relation!(SignedNatTableElements, 1);

const SIGNED_VALID_COUNT: usize = ASSIGNED_ISO_ALPHA2.len() + 2;
const SIGNED_VALID_LOG_SIZE: u32 = 9;

/// Defines the base for reserved dummy keys in the accepted-set table.
///
/// All valid ISO-numeric and packed alpha-2 codes are below this base.
/// Thus, valid membership values cannot equal dummy keys.
const NAT_DUMMY_KEY_BASE: u32 = 1 << 24;

/// Returns the preprocessed accepted-set table ID.
///
/// The ID includes the code space and exact accepted codes.
/// Thus, shared modules with this ID use the same fixed table.
/// The fingerprint guard rejects different content under one ID.
///
/// This is the Class-D **blinded** value column id (real codes in the reachable
/// prefix, reserved dummy keys in the suffix). Namespaced with `blind/` so it
/// never aliases a non-blinded table of the same accepted set.
pub fn acceptable_col_id(public: &PublicInput) -> PreProcessedColumnId {
    let ids: Vec<String> = public.acceptable.iter().map(|c| c.to_string()).collect();
    PreProcessedColumnId {
        id: format!("nat/acceptable/blind/alpha2/{}", ids.join(",")),
    }
}

/// Preprocessed `is_dummy` selector id for the blinded accepted-set table: `1`
/// over the reserved dummy suffix, `0` over the reachable prefix.
pub fn acceptable_dummy_col_id(public: &PublicInput) -> PreProcessedColumnId {
    let ids: Vec<String> = public.acceptable.iter().map(|c| c.to_string()).collect();
    PreProcessedColumnId {
        id: format!("nat/acceptable/dummy/alpha2/{}", ids.join(",")),
    }
}

pub fn signed_valid_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "nat/signed-valid/blind/iso-alpha2-plus-qu-qs".into(),
    }
}

pub fn signed_valid_dummy_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "nat/signed-valid/dummy/iso-alpha2-plus-qu-qs".into(),
    }
}

/// Committed row count of the Class-D blinded table, extended to the minimum
/// claim-mask domain when the accepted set is small.
pub fn blind_log_size(public: &PublicInput) -> u32 {
    (public.log_size() + 1)
        .max(CLAIM_MASK_MIN_LOG_SIZE)
        .max(SIGNED_VALID_LOG_SIZE)
}

/// Class-D blinded value column: accepted codes occupy exactly the reachable
/// prefix. Every remaining row carries a reserved dummy key.
pub fn acceptable_value_column(public: &PublicInput) -> Column {
    let total = 1usize << blind_log_size(public);
    let domain = CanonicCoset::new(blind_log_size(public)).circle_domain();
    let mut col = BaseColumn::zeros(total);
    for (i, &code) in public.acceptable.iter().enumerate() {
        col.set(i, M31::from_u32_unchecked(code));
    }
    for i in 0..total - public.acceptable.len() {
        col.set(
            public.acceptable.len() + i,
            M31::from_u32_unchecked(NAT_DUMMY_KEY_BASE + i as u32),
        );
    }
    CircleEvaluation::new(domain, col)
}

/// Class-D `is_dummy` selector: `0` over the reachable prefix and `1` over the
/// dummy suffix.
pub fn acceptable_dummy_column(public: &PublicInput) -> Column {
    let total = 1usize << blind_log_size(public);
    let domain = CanonicCoset::new(blind_log_size(public)).circle_domain();
    let mut col = BaseColumn::zeros(total);
    for i in public.acceptable.len()..total {
        col.set(i, M31::one());
    }
    CircleEvaluation::new(domain, col)
}

/// Builds a Class-D blinded multiplicity column.
///
/// Used accepted-code rows contain their signed entry count.
/// Unused real rows contain zero.
/// Dummy rows contain fresh random cells.
pub fn gen_blind_multiplicity_column(public: &PublicInput, used_rows: &[usize]) -> Column {
    let size = 1usize << blind_log_size(public);
    let mut data = vec![M31::zero(); size];
    for &used_row in used_rows {
        data[used_row] += M31::one();
    }
    for slot in data.iter_mut().skip(public.acceptable.len()) {
        *slot = random_m31_cell();
    }
    CircleEvaluation::new(
        CanonicCoset::new(blind_log_size(public)).circle_domain(),
        BaseColumn::from_iter(data),
    )
}

pub fn signed_valid_value_column(public: &PublicInput) -> Column {
    let log_size = blind_log_size(public);
    let size = 1usize << log_size;
    let mut data = vec![M31::zero(); size];
    for (row, code) in signed_alpha2_codes().enumerate() {
        data[row] = M31::from_u32_unchecked(code);
    }
    for row in SIGNED_VALID_COUNT..size {
        data[row] = M31::from_u32_unchecked(NAT_DUMMY_KEY_BASE + row as u32);
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(data),
    )
}

pub fn signed_valid_dummy_column(public: &PublicInput) -> Column {
    let log_size = blind_log_size(public);
    let size = 1usize << log_size;
    let mut data = vec![M31::zero(); size];
    data[SIGNED_VALID_COUNT..].fill(M31::one());
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(data),
    )
}

pub fn gen_signed_valid_multiplicity_column(public: &PublicInput, codes: &[u32]) -> Column {
    let log_size = blind_log_size(public);
    let size = 1usize << log_size;
    let valid_codes = signed_alpha2_codes().collect::<Vec<_>>();
    let mut data = vec![M31::zero(); size];
    for code in codes {
        if let Some(row) = valid_codes.iter().position(|valid| valid == code) {
            data[row] += M31::one();
        }
    }
    for slot in &mut data[SIGNED_VALID_COUNT..] {
        *slot = random_m31_cell();
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(data),
    )
}

/// Provides a Class-D multiplicity-blinded accepted-set table.
///
/// Reads the blinded value column and the `is_dummy` selector.
/// The reachable prefix contains accepted codes.
/// The suffix contains reserved dummy keys.
/// Each row emits one gated shared-relation entry.
/// Its numerator is `-(1 − is_dummy) · multiplicity`.
///
/// A real row has numerator `-multiplicity`.
/// This is the same value as the unblinded table.
/// A dummy row has numerator `0` for every random multiplicity.
/// Thus, blind multiplicities do not change the global balance.
/// Honest consumers cannot use dummy keys because valid codes are below `2^24`.
///
/// The trusted `is_dummy` selector prevents a prover from activating a dummy row.
/// `(1 − is_dummy) · multiplicity` is preprocessed × trace = degree 2, within `D ≤ 3`.
#[derive(Clone)]
pub struct NatTableEval {
    pub public: PublicInput,
    pub accepted_elements: NatTableElements,
    pub signed_valid_elements: SignedNatTableElements,
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
        let accepted_is_dummy = eval.get_preprocessed_column(acceptable_dummy_col_id(&self.public));
        let signed_nat_code = eval.get_preprocessed_column(signed_valid_col_id());
        let signed_is_dummy = eval.get_preprocessed_column(signed_valid_dummy_col_id());
        let accepted_mult = eval.next_trace_mask();
        let signed_mult = eval.next_trace_mask();
        // Single gated membership yield `-(1 − is_dummy)·mult`: `-m` on real rows
        // (is_dummy = 0), identically `0` on dummy rows for any committed `m`.
        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_to_relation(RelationEntry::new(
            &self.accepted_elements,
            -E::EF::from((one.clone() - accepted_is_dummy) * accepted_mult),
            std::slice::from_ref(&acc_nat_code),
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.signed_valid_elements,
            -E::EF::from((one - signed_is_dummy) * signed_mult),
            std::slice::from_ref(&signed_nat_code),
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[cfg(test)]
mod class_d_tests {
    use super::*;

    fn public() -> PublicInput {
        PublicInput::new(vec![0x4445, 0x4652, 0x4752])
    }

    /// Confirms that only exact accepted-set rows are reachable.
    #[test]
    fn blinded_table_reserves_unreachable_dummy_keys() {
        let public = public();
        let real = public.acceptable.len();
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

    /// Random dummy multiplicities live only outside the exact accepted set.
    /// Their gated numerators are zero, so they do not change the relation
    /// balance. Each generation still randomizes the committed dummy suffix.
    /// This algebraic test does not claim transcript-wide confidentiality.
    #[test]
    fn dummy_multiplicity_suffix_is_fresh_and_relation_neutral() {
        let public = public();
        let real = public.acceptable.len();
        let used_row = 1usize; // FR sits at sorted index 1.

        let first = gen_blind_multiplicity_column(&public, &[used_row]);
        let second = gen_blind_multiplicity_column(&public, &[used_row]);
        assert_eq!(
            first.values.at(used_row).0,
            1,
            "the used code's real count is 1"
        );
        // Every dummy row is fresh randomness that differs across runs.
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

    #[test]
    fn signed_valid_table_contains_exact_fixed_domain() {
        let public = PublicInput::new(vec![0x4445]);
        let values = signed_valid_value_column(&public);
        let dummy = signed_valid_dummy_column(&public);
        let expected = signed_alpha2_codes().collect::<Vec<_>>();

        assert_eq!(expected.len(), 251);
        assert!(expected.windows(2).all(|pair| pair[0] < pair[1]));
        for (row, code) in expected.into_iter().enumerate() {
            assert_eq!(values.values.at(row).0, code);
            assert_eq!(dummy.values.at(row).0, 0);
        }
        for row in SIGNED_VALID_COUNT..1 << blind_log_size(&public) {
            assert_eq!(dummy.values.at(row).0, 1);
            assert!(values.values.at(row).0 >= NAT_DUMMY_KEY_BASE);
        }
    }

    #[test]
    fn public_and_signed_tables_share_one_domain() {
        for public in [
            PublicInput::new(vec![0x4445]),
            PublicInput::new(
                ASSIGNED_ISO_ALPHA2
                    .iter()
                    .copied()
                    .map(crate::nat::nationalities::pack_alpha2)
                    .collect(),
            ),
        ] {
            let expected = blind_log_size(&public);
            assert_eq!(acceptable_value_column(&public).domain.log_size(), expected);
            assert_eq!(acceptable_dummy_column(&public).domain.log_size(), expected);
            assert_eq!(
                signed_valid_value_column(&public).domain.log_size(),
                expected
            );
            assert_eq!(
                signed_valid_dummy_column(&public).domain.log_size(),
                expected
            );
            assert_eq!(
                gen_signed_valid_multiplicity_column(&public, &[0x4445])
                    .domain
                    .log_size(),
                expected
            );
        }
    }
}
