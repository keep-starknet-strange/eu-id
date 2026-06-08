use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    proof::StarkProof,
    ColumnVec,
};
use stwo::prover::backend::simd::{
            m31::{PackedM31, LOG_N_LANES},
            qm31::PackedQM31,
        };
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

use crate::scalar::fake_glv_chain::{FakeGlvChainClaim, FakeGlvChainError, FakeGlvChainRow};
use crate::scalar::prepared_table::{
    prepared_table_ec_point_values, PreparedAffinePoint, PreparedTableEcEvalPoint,
    PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

relation!(
    FakeGlvChainAccumulatorRelation,
    FAKE_GLV_CHAIN_ACCUMULATOR_RELATION_ARITY
);

pub type FakeGlvChainContinuityComponent = FrameworkComponent<FakeGlvChainContinuityEval>;

pub const FAKE_GLV_CHAIN_ACCUMULATOR_RELATION_ARITY: usize = 3 + PREPARED_TABLE_EC_POINT_COLUMNS;
pub const FAKE_GLV_CHAIN_CONTINUITY_TRACE_COLUMNS: usize = 8 + 4 * PREPARED_TABLE_EC_POINT_COLUMNS;

const FAKE_GLV_CHAIN_ROW_INDEX_COLUMN: &str = "p256_fake_glv_chain_row_index";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvChainContinuityProofClaim {
    pub log_size: u32,
}

impl FakeGlvChainContinuityProofClaim {
    pub fn from_chain(chain: &FakeGlvChainClaim) -> Self {
        Self {
            log_size: padded_log_size(chain.active_row_count()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvChainContinuityComponent::new(
            &mut allocator,
            FakeGlvChainContinuityEval {
                log_size: self.log_size,
                relation: FakeGlvChainAccumulatorRelation::dummy(),
            },
            secure_zero(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = FakeGlvChainContinuityComponent::new(
            &mut allocator,
            FakeGlvChainContinuityEval {
                log_size: self.log_size,
                relation: FakeGlvChainAccumulatorRelation::dummy(),
            },
            secure_zero(),
        );
        component.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = FakeGlvChainContinuityComponent::new(
            &mut allocator,
            FakeGlvChainContinuityEval {
                log_size: self.log_size,
                relation: FakeGlvChainAccumulatorRelation::dummy(),
            },
            secure_zero(),
        );
        component.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvChainContinuityInteractionClaim {
    pub claimed_sum: SecureField,
}

impl FakeGlvChainContinuityInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

#[derive(Clone, Debug)]
pub struct FakeGlvChainContinuityProof<H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>
{
    pub claim: FakeGlvChainContinuityProofClaim,
    pub interaction_claim: FakeGlvChainContinuityInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

#[derive(Clone)]
pub struct FakeGlvChainContinuityEval {
    pub log_size: u32,
    pub relation: FakeGlvChainAccumulatorRelation,
}

impl FrameworkEval for FakeGlvChainContinuityEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let preprocessed_row_index =
            eval.get_preprocessed_column(fake_glv_chain_row_index_column_id());
        let row_index = eval.next_trace_mask();
        let active = eval.next_trace_mask();
        let has_prev = eval.next_trace_mask();
        let has_next = eval.next_trace_mask();
        let is_first = eval.next_trace_mask();
        let is_last = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let acc_before = PreparedTableEcEvalPoint::read(&mut eval);
        let operand = PreparedTableEcEvalPoint::read(&mut eval);
        let acc_after = PreparedTableEcEvalPoint::read(&mut eval);
        let r3 = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        for flag in [
            active.clone(),
            has_prev.clone(),
            has_next.clone(),
            is_first.clone(),
            is_last.clone(),
        ] {
            eval.add_constraint(flag.clone() * (flag - one.clone()));
        }
        eval.add_constraint(active.clone() * (row_index.clone() - preprocessed_row_index));
        eval.add_constraint(has_prev.clone() + is_first.clone() - active.clone());
        eval.add_constraint(has_next.clone() + is_last.clone() - active.clone());
        for value in [row_index.clone(), sig_id.clone(), cert_id.clone()] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        acc_before.add_constraints(&mut eval, &active, &one);
        operand.add_constraints(&mut eval, &active, &one);
        acc_after.add_constraints(&mut eval, &active, &one);
        r3.add_constraints(&mut eval, &is_last, &one);

        for (actual, expected) in acc_before
            .relation_values()
            .into_iter()
            .zip(infinity_relation_values())
        {
            eval.add_constraint(is_first.clone() * (actual - expected));
        }
        for (after, operand) in acc_after
            .relation_values()
            .into_iter()
            .zip(operand.relation_values())
        {
            eval.add_constraint(is_first.clone() * (after - operand));
        }
        for (after, r3) in acc_after
            .relation_values()
            .into_iter()
            .zip(r3.relation_values())
        {
            eval.add_constraint(is_last.clone() * (after - r3));
        }

        let provider_values = fake_glv_chain_accumulator_relation_values(
            &[row_index.clone() + one, sig_id.clone(), cert_id.clone()],
            &acc_after,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(has_next),
            &provider_values,
        ));

        let consumer_values =
            fake_glv_chain_accumulator_relation_values(&[row_index, sig_id, cert_id], &acc_before);
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(has_prev),
            &consumer_values,
        ));
        eval.finalize_logup();
        eval
    }
}

pub(crate) fn gen_fake_glv_chain_continuity_preprocessed_trace(
    log_size: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if id == &fake_glv_chain_row_index_column_id() {
                Ok(m31_column_eval(
                    log_size,
                    (0..(1usize << log_size))
                        .map(|index| M31::from_u32_unchecked(index as u32))
                        .collect(),
                ))
            } else {
                Err(FakeGlvChainError::PreprocessedColumnMissing)
            }
        })
        .collect()
}

pub(crate) fn gen_fake_glv_chain_continuity_base_trace(
    chain: &FakeGlvChainClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    if chain.active_row_count() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: chain.active_row_count(),
            domain: padded_rows,
        });
    }
    let mut rows = Vec::with_capacity(chain.active_row_count());
    for cert in &chain.certs {
        let row_count = cert.rows.len();
        for (index, row) in cert.rows.iter().enumerate() {
            let row_index = rows.len();
            rows.push(fake_glv_chain_continuity_trace_values(
                row, &cert.r3, row_index, index, row_count,
            ));
        }
    }
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_CHAIN_CONTINUITY_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_fake_glv_chain_continuity_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvChainAccumulatorRelation,
) -> (
    ColumnVec<M31ColumnEval>,
    FakeGlvChainContinuityInteractionClaim,
) {
    assert_eq!(base.len(), FAKE_GLV_CHAIN_CONTINUITY_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut provider_col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = fake_glv_chain_provider_packed_relation_values(base, vec_row);
        let numerator = -PackedQM31::from(base[3].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        provider_col.write_frac(vec_row, numerator, denominator);
    }
    provider_col.finalize_col();

    let mut consumer_col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = fake_glv_chain_consumer_packed_relation_values(base, vec_row);
        let numerator = PackedQM31::from(base[2].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        consumer_col.write_frac(vec_row, numerator, denominator);
    }
    consumer_col.finalize_col();

    let (trace, claimed_sum) = logup.finalize_last();
    (
        trace,
        FakeGlvChainContinuityInteractionClaim { claimed_sum },
    )
}

fn fake_glv_chain_continuity_trace_values(
    row: &FakeGlvChainRow,
    r3: &PreparedAffinePoint,
    row_index: usize,
    index: usize,
    row_count: usize,
) -> [M31; FAKE_GLV_CHAIN_CONTINUITY_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); FAKE_GLV_CHAIN_CONTINUITY_TRACE_COLUMNS];
    let is_first = index == 0;
    let is_last = index + 1 == row_count;
    values[0] = M31::from_u32_unchecked(row_index as u32);
    values[1] = M31::from_u32_unchecked(1);
    values[2] = M31::from_u32_unchecked(u32::from(!is_first));
    values[3] = M31::from_u32_unchecked(u32::from(!is_last));
    values[4] = M31::from_u32_unchecked(u32::from(is_first));
    values[5] = M31::from_u32_unchecked(u32::from(is_last));
    values[6] = row.sig_id;
    values[7] = row.cert_id;
    let mut column = 8;
    for point in [&row.acc_before, &row.operand, &row.acc_after] {
        for value in prepared_table_ec_point_values(point) {
            values[column] = value;
            column += 1;
        }
    }
    let r3_values = if is_last {
        prepared_table_ec_point_values(r3)
    } else {
        [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_POINT_COLUMNS]
    };
    for value in r3_values {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, FAKE_GLV_CHAIN_CONTINUITY_TRACE_COLUMNS);
    values
}

fn fake_glv_chain_accumulator_relation_values<F: Clone>(
    header: &[F; 3],
    point: &PreparedTableEcEvalPoint<F>,
) -> [F; FAKE_GLV_CHAIN_ACCUMULATOR_RELATION_ARITY] {
    fake_glv_chain_accumulator_values(header, &point.relation_values())
}

fn fake_glv_chain_accumulator_values<F: Clone>(
    header: &[F; 3],
    point: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
) -> [F; FAKE_GLV_CHAIN_ACCUMULATOR_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0..=2 => header[index].clone(),
        3..=43 => point[index - 3].clone(),
        _ => unreachable!("fake-GLV chain accumulator relation index is in range"),
    })
}

fn fake_glv_chain_provider_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_CHAIN_ACCUMULATOR_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => None,
            1 => Some(6),
            2 => Some(7),
            3..=43 => Some(90 + (index - 3)),
            _ => unreachable!("fake-GLV chain accumulator relation index is in range"),
        };
        match column {
            Some(column) => base[column].data[vec_row],
            None => base[0].data[vec_row] + PackedM31::from(M31::from_u32_unchecked(1)),
        }
    })
}

fn fake_glv_chain_consumer_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_CHAIN_ACCUMULATOR_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => None,
            1 => Some(6),
            2 => Some(7),
            3..=43 => Some(8 + (index - 3)),
            _ => unreachable!("fake-GLV chain accumulator relation index is in range"),
        };
        match column {
            Some(column) => base[column].data[vec_row],
            None => base[0].data[vec_row],
        }
    })
}

fn infinity_relation_values<F>() -> [F; PREPARED_TABLE_EC_POINT_COLUMNS]
where
    F: Clone + From<M31>,
{
    core::array::from_fn(|index| {
        if index == PREPARED_TABLE_EC_POINT_COLUMNS - 1 {
            F::from(M31::from_u32_unchecked(1))
        } else {
            F::from(M31::from_u32_unchecked(0))
        }
    })
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
}

fn fake_glv_chain_row_index_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: FAKE_GLV_CHAIN_ROW_INDEX_COLUMN.into(),
    }
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}
