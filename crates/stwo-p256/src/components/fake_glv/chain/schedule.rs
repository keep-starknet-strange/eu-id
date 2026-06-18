use serde::{Deserialize, Serialize};
use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    proof::StarkProof,
    ColumnVec,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
};

use crate::scalar::fake_glv_chain::{FakeGlvChainClaim, FakeGlvChainError, FakeGlvChainRowKind};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

pub type FakeGlvChainScheduleComponent = FrameworkComponent<FakeGlvChainScheduleEval>;

pub const FAKE_GLV_CHAIN_ROWS_PER_ACTIVE_CERT: usize = 65;
pub const FAKE_GLV_CHAIN_MSB_PHASE: usize = 0;
pub const FAKE_GLV_CHAIN_CHAIN_FIRST_PHASE: usize = 1;
pub const FAKE_GLV_CHAIN_CHAIN_LAST_PHASE: usize = 62;
pub const FAKE_GLV_CHAIN_TABLE16_PHASE: usize = 63;
pub const FAKE_GLV_CHAIN_LSB_PHASE: usize = 64;
pub const FAKE_GLV_CHAIN_SCHEDULE_TRACE_COLUMNS: usize = 8;

const EXPECTED_MSB_INIT_COLUMN: &str = "p256_fake_glv_chain_expected_msb_init";
const EXPECTED_CHAIN_STEP_COLUMN: &str = "p256_fake_glv_chain_expected_chain_step";
const EXPECTED_TABLE16_STEP_COLUMN: &str = "p256_fake_glv_chain_expected_table16_step";
const EXPECTED_LSB_CORRECTION_COLUMN: &str = "p256_fake_glv_chain_expected_lsb_correction";
const EXPECTED_CHAIN_STEP_INDEX_COLUMN: &str = "p256_fake_glv_chain_expected_chain_step_index";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvChainScheduleProofClaim {
    pub log_size: u32,
}

impl FakeGlvChainScheduleProofClaim {
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
        let _ = FakeGlvChainScheduleComponent::new(
            &mut allocator,
            FakeGlvChainScheduleEval {
                log_size: self.log_size,
            },
            secure_zero(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = FakeGlvChainScheduleComponent::new(
            &mut allocator,
            FakeGlvChainScheduleEval {
                log_size: self.log_size,
            },
            secure_zero(),
        );
        component.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = FakeGlvChainScheduleComponent::new(
            &mut allocator,
            FakeGlvChainScheduleEval {
                log_size: self.log_size,
            },
            secure_zero(),
        );
        component.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Debug)]
pub struct FakeGlvChainScheduleProof<H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted> {
    pub claim: FakeGlvChainScheduleProofClaim,
    pub stark_proof: StarkProof<H>,
}

#[derive(Clone)]
pub struct FakeGlvChainScheduleEval {
    pub log_size: u32,
}

impl FrameworkEval for FakeGlvChainScheduleEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let expected_msb = eval.get_preprocessed_column(expected_msb_init_column_id());
        let expected_chain = eval.get_preprocessed_column(expected_chain_step_column_id());
        let expected_table16 = eval.get_preprocessed_column(expected_table16_step_column_id());
        let expected_lsb = eval.get_preprocessed_column(expected_lsb_correction_column_id());
        let expected_step = eval.get_preprocessed_column(expected_chain_step_index_column_id());
        let active = eval.next_trace_mask();
        let is_msb = eval.next_trace_mask();
        let is_chain = eval.next_trace_mask();
        let is_table16 = eval.next_trace_mask();
        let is_lsb = eval.next_trace_mask();
        let chain_step = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let one = E::F::from(M31::from_u32_unchecked(1));

        for flag in [
            active.clone(),
            is_msb.clone(),
            is_chain.clone(),
            is_table16.clone(),
            is_lsb.clone(),
        ] {
            eval.add_constraint(flag.clone() * (flag - one.clone()));
        }
        eval.add_constraint(
            is_msb.clone() + is_chain.clone() + is_table16.clone() + is_lsb.clone()
                - active.clone(),
        );
        eval.add_constraint(active.clone() * (is_msb - expected_msb));
        eval.add_constraint(active.clone() * (is_chain - expected_chain));
        eval.add_constraint(active.clone() * (is_table16 - expected_table16));
        eval.add_constraint(active.clone() * (is_lsb - expected_lsb));
        eval.add_constraint(active.clone() * (chain_step.clone() - expected_step));
        for value in [chain_step.clone(), sig_id, cert_id] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        eval
    }
}

pub(crate) fn gen_fake_glv_chain_schedule_preprocessed_trace(
    log_size: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if !is_expected_schedule_column(id) {
                return Err(FakeGlvChainError::PreprocessedColumnMissing);
            }
            let rows = (0..(1usize << log_size))
                .map(|index| expected_schedule_value(id, index))
                .collect();
            Ok(m31_column_eval(log_size, rows))
        })
        .collect()
}

pub(crate) fn gen_fake_glv_chain_schedule_base_trace(
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
    let mut rows = chain
        .certs
        .iter()
        .flat_map(|cert| cert.rows.iter())
        .map(fake_glv_chain_schedule_trace_values)
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_CHAIN_SCHEDULE_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn fake_glv_chain_schedule_trace_values(
    row: &crate::scalar::fake_glv_chain::FakeGlvChainRow,
) -> [M31; FAKE_GLV_CHAIN_SCHEDULE_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); FAKE_GLV_CHAIN_SCHEDULE_TRACE_COLUMNS];
    values[0] = M31::from_u32_unchecked(1);
    values[6] = row.sig_id;
    values[7] = row.cert_id;
    match row.kind {
        FakeGlvChainRowKind::MsbInit => values[1] = M31::from_u32_unchecked(1),
        FakeGlvChainRowKind::ChainStep(step) => {
            values[2] = M31::from_u32_unchecked(1);
            values[5] = M31::from_u32_unchecked(step);
        }
        FakeGlvChainRowKind::Table16Step => values[3] = M31::from_u32_unchecked(1),
        FakeGlvChainRowKind::LsbCorrection => values[4] = M31::from_u32_unchecked(1),
    }
    values
}

fn expected_schedule_value(id: &PreProcessedColumnId, row_index: usize) -> M31 {
    let local_index = row_index % FAKE_GLV_CHAIN_ROWS_PER_ACTIVE_CERT;
    let value = if id == &expected_msb_init_column_id() {
        u32::from(local_index == FAKE_GLV_CHAIN_MSB_PHASE)
    } else if id == &expected_chain_step_column_id() {
        u32::from(
            (FAKE_GLV_CHAIN_CHAIN_FIRST_PHASE..=FAKE_GLV_CHAIN_CHAIN_LAST_PHASE)
                .contains(&local_index),
        )
    } else if id == &expected_table16_step_column_id() {
        u32::from(local_index == FAKE_GLV_CHAIN_TABLE16_PHASE)
    } else if id == &expected_lsb_correction_column_id() {
        u32::from(local_index == FAKE_GLV_CHAIN_LSB_PHASE)
    } else if id == &expected_chain_step_index_column_id() {
        if (FAKE_GLV_CHAIN_CHAIN_FIRST_PHASE..=FAKE_GLV_CHAIN_CHAIN_LAST_PHASE)
            .contains(&local_index)
        {
            (FAKE_GLV_CHAIN_ROWS_PER_ACTIVE_CERT - 2 - local_index) as u32
        } else {
            0
        }
    } else {
        unreachable!("fake-GLV chain schedule column id was checked");
    };
    M31::from_u32_unchecked(value)
}

fn is_expected_schedule_column(id: &PreProcessedColumnId) -> bool {
    id == &expected_msb_init_column_id()
        || id == &expected_chain_step_column_id()
        || id == &expected_table16_step_column_id()
        || id == &expected_lsb_correction_column_id()
        || id == &expected_chain_step_index_column_id()
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
}

fn expected_msb_init_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: EXPECTED_MSB_INIT_COLUMN.into(),
    }
}

fn expected_chain_step_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: EXPECTED_CHAIN_STEP_COLUMN.into(),
    }
}

fn expected_table16_step_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: EXPECTED_TABLE16_STEP_COLUMN.into(),
    }
}

fn expected_lsb_correction_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: EXPECTED_LSB_CORRECTION_COLUMN.into(),
    }
}

fn expected_chain_step_index_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: EXPECTED_CHAIN_STEP_INDEX_COLUMN.into(),
    }
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}
