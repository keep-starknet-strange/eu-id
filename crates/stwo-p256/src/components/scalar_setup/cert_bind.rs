use std::fmt;

use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::{
    backend::simd::{
        m31::{PackedM31, LOG_N_LANES},
        qm31::PackedQM31,
        SimdBackend,
    },
    ComponentProver,
};
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::N_LIMBS;

use crate::constants::{P256_GX, P256_GY};
use crate::limbs::{P256BigInt, P256M31BigInt};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::U256;

use crate::scalar::prepared_table::{CertBaseRelation, CERT_BASE_RELATION_ARITY};
use crate::scalar::setup_air::{
    ScalarSetupClaim, ScalarSetupOutput, ScalarSetupOutputRelation, SCALAR_SETUP_OUTPUT_ARITY,
};

pub const CERT_ID_U1_GENERATOR: u32 = 0;
pub const CERT_ID_U2_PUBLIC_KEY: u32 = 1;
pub const CERT_SCALAR_INPUT_RELATION_ARITY: usize = 2 + 3 * N_LIMBS + 1 + 4;

/// Number of prepared-table cells that must equal the cert base point `P` per
/// cert. cert0 (generator) has no `DoubleP`/`AddP2P` rows, so only `Base(1,2,5,6)`
/// reference `P` (4 cells). cert1 (public key) adds `DoubleP.lhs` and `AddP2P.rhs`
/// (6 cells). The cert-base provider yields `-count·cert_active` to balance the
/// per-cell consumers in `PreparedTableEcRowEval`.
pub const CERT0_PREPARED_P_CELL_COUNT: u32 = 4;
pub const CERT1_PREPARED_P_CELL_COUNT: u32 = 6;

relation!(
    CertScalarInputRelation,
    CERT_SCALAR_INPUT_RELATION_ARITY
);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertScalarInputClaim {
    pub rows: Vec<CertScalarInputRow>,
}

impl CertScalarInputClaim {
    pub fn from_scalar_setup(
        scalar_setup: &ScalarSetupClaim,
    ) -> Result<Self, CertScalarInputError> {
        let mut rows = Vec::with_capacity(2 * scalar_setup.rows.len());
        for row in &scalar_setup.rows {
            rows.push(CertScalarInputRow::from_scalar_setup_output(
                &row.output,
                CertificateScalarSource::U1Generator,
            ));
            rows.push(CertScalarInputRow::from_scalar_setup_output(
                &row.output,
                CertificateScalarSource::U2PublicKey,
            ));
        }
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), CertScalarInputError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.rows.len() as u64);
        for row in &self.rows {
            channel.mix_u64(row.sig_id.0 as u64);
            channel.mix_u64(row.cert_id.0 as u64);
        }
    }
}

pub type CertScalarInputAirComponent = FrameworkComponent<CertScalarInputAirEval>;

pub const CERT_SCALAR_INPUT_TRACE_COLUMNS: usize =
    1 + SCALAR_SETUP_OUTPUT_ARITY + 2 * CERT_SCALAR_INPUT_ROW_COLUMNS + 2;
const CERT_SCALAR_INPUT_ROW_COLUMNS: usize = 2 + 3 * N_LIMBS + 1 + 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertScalarInputAirProofClaim {
    pub log_size: u32,
}

impl CertScalarInputAirProofClaim {
    pub fn from_claim(claim: &ScalarSetupClaim) -> Self {
        Self {
            log_size: padded_log_size(claim.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertScalarInputAirInteractionClaim {
    pub claimed_sum: SecureField,
    pub scalar_setup_consumer_claimed_sum: SecureField,
    pub cert_provider_claimed_sum: SecureField,
    /// Yield of `CertBaseRelation` (prepared-table base pinning). Zero unless the
    /// cert-base provider is active (monolithic STARK).
    pub cert_base_provider_claimed_sum: SecureField,
}

impl CertScalarInputAirInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
            scalar_setup_consumer_claimed_sum: secure_zero(),
            cert_provider_claimed_sum: secure_zero(),
            cert_base_provider_claimed_sum: secure_zero(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub struct CertScalarInputAirComponents {
    pub certs: CertScalarInputAirComponent,
}

impl CertScalarInputAirComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: CertScalarInputAirProofClaim,
        interaction_claim: &CertScalarInputAirInteractionClaim,
        relation: &ScalarSetupOutputRelation,
        cert_relation: &CertScalarInputRelation,
        cert_base_relation: Option<&CertBaseRelation>,
    ) -> Self {
        Self {
            certs: CertScalarInputAirComponent::new(
                allocator,
                CertScalarInputAirEval {
                    log_size: claim.log_size,
                    scalar_setup_output: relation.clone(),
                    cert_relation: cert_relation.clone(),
                    cert_base_relation: cert_base_relation.cloned(),
                },
                interaction_claim.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![&self.certs as &dyn Component]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.certs as &dyn ComponentProver<SimdBackend>]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        self.certs.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.certs.max_constraint_log_degree_bound()
    }
}

#[derive(Clone)]
pub struct CertScalarInputAirEval {
    pub log_size: u32,
    pub scalar_setup_output: ScalarSetupOutputRelation,
    pub cert_relation: CertScalarInputRelation,
    /// Provides `CertBaseRelation` for prepared-table base pinning. `Some` in the
    /// monolithic STARK (consumed by `PreparedTableEcRowEval`); `None` for the
    /// standalone cert slice. Yields `-m(cert_id)·cert_active` where `m` is the
    /// number of prepared-table cells that must equal `P` (cert0: 4, cert1: 6).
    pub cert_base_relation: Option<CertBaseRelation>,
}

impl FrameworkEval for CertScalarInputAirEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let setup = read_scalar_setup_output(&mut eval);
        let cert0 = read_cert_scalar_input_air_row(&mut eval);
        let cert1 = read_cert_scalar_input_air_row(&mut eval);
        let cert0_inv = eval.next_trace_mask();
        let cert1_inv = eval.next_trace_mask();
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        for value in setup.relation_values() {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }
        constrain_cert_padding(&mut eval, active.clone(), &cert0);
        constrain_cert_padding(&mut eval, active.clone(), &cert1);

        eval.add_to_relation(RelationEntry::new(
            &self.scalar_setup_output,
            E::EF::from(active.clone()),
            &setup.relation_values(),
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.cert_relation,
            -E::EF::from(active.clone()),
            &cert0.relation_values(),
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.cert_relation,
            -E::EF::from(active.clone()),
            &cert1.relation_values(),
        ));

        if let Some(cert_base_relation) = &self.cert_base_relation {
            // Yield the base point `-m(cert_id)·cert_active` times so the
            // prepared-table P-cell consumers (use +1) balance exactly.
            eval.add_to_relation(RelationEntry::new(
                cert_base_relation,
                -E::EF::from(
                    cert0.cert_active.clone()
                        * E::F::from(M31::from_u32_unchecked(CERT0_PREPARED_P_CELL_COUNT)),
                ),
                &cert_base_relation_values_from_row(&cert0),
            ));
            eval.add_to_relation(RelationEntry::new(
                cert_base_relation,
                -E::EF::from(
                    cert1.cert_active.clone()
                        * E::F::from(M31::from_u32_unchecked(CERT1_PREPARED_P_CELL_COUNT)),
                ),
                &cert_base_relation_values_from_row(&cert1),
            ));
        }

        constrain_cert_from_setup(
            &mut eval,
            active.clone(),
            &setup,
            &cert0,
            CertificateScalarSource::U1Generator,
            cert0_inv,
        );
        constrain_cert_from_setup(
            &mut eval,
            active,
            &setup,
            &cert1,
            CertificateScalarSource::U2PublicKey,
            cert1_inv,
        );

        eval.finalize_logup();
        eval
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertScalarInputRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub scalar: P256M31BigInt,
    pub base_x: P256M31BigInt,
    pub base_y: P256M31BigInt,
    pub base_inf: M31,
    pub scalar_is_zero: M31,
    pub scalar_is_nonzero: M31,
    pub cert_active: M31,
    pub cert_zero_active: M31,
}

impl CertScalarInputRow {
    pub fn from_scalar_setup_output(
        output: &ScalarSetupOutput<M31>,
        source: CertificateScalarSource,
    ) -> Self {
        let scalar = match source {
            CertificateScalarSource::U1Generator => output.u1.clone(),
            CertificateScalarSource::U2PublicKey => output.u2.clone(),
        };
        let scalar_is_zero = m31_bool(is_zero_bigint(&scalar));
        let scalar_is_nonzero = m31_bool(!is_zero_bigint(&scalar));
        Self {
            sig_id: output.sig_id,
            cert_id: M31::from_u32_unchecked(source.cert_id()),
            base_x: source.base_x(output),
            base_y: source.base_y(output),
            base_inf: M31::from_u32_unchecked(0),
            scalar,
            scalar_is_zero,
            scalar_is_nonzero,
            cert_active: scalar_is_nonzero,
            cert_zero_active: scalar_is_zero,
        }
    }

    pub fn verify(&self) -> Result<(), CertScalarInputError> {
        require_bool("scalar_is_zero", self.scalar_is_zero)?;
        require_bool("scalar_is_nonzero", self.scalar_is_nonzero)?;
        require_bool("cert_active", self.cert_active)?;
        require_bool("cert_zero_active", self.cert_zero_active)?;
        require_eq(
            "scalar_is_zero + scalar_is_nonzero",
            self.scalar_is_zero.0 + self.scalar_is_nonzero.0,
            1,
        )?;
        let scalar_zero = is_zero_bigint(&self.scalar);
        require_eq(
            "scalar_is_zero",
            self.scalar_is_zero.0,
            u32::from(scalar_zero),
        )?;
        require_eq(
            "scalar_is_nonzero",
            self.scalar_is_nonzero.0,
            u32::from(!scalar_zero),
        )?;
        require_eq("cert_active", self.cert_active.0, self.scalar_is_nonzero.0)?;
        require_eq(
            "cert_zero_active",
            self.cert_zero_active.0,
            self.scalar_is_zero.0,
        )?;
        require_eq("base_inf", self.base_inf.0, 0)?;
        if self.cert_id.0 == CERT_ID_U2_PUBLIC_KEY && scalar_zero {
            return Err(CertScalarInputError::UnexpectedZeroU2 {
                sig_id: self.sig_id.0,
            });
        }
        Ok(())
    }
}

#[derive(Clone)]
struct CertScalarInputAirRow<F> {
    sig_id: F,
    cert_id: F,
    scalar: P256BigInt<F>,
    base_x: P256BigInt<F>,
    base_y: P256BigInt<F>,
    base_inf: F,
    scalar_is_zero: F,
    scalar_is_nonzero: F,
    cert_active: F,
    cert_zero_active: F,
}

impl<F: Clone> CertScalarInputAirRow<F> {
    fn relation_values(&self) -> [F; CERT_SCALAR_INPUT_RELATION_ARITY] {
        core::array::from_fn(|index| self.relation_value(index))
    }

    fn relation_value(&self, index: usize) -> F {
        if index == 0 {
            return self.sig_id.clone();
        }
        if index == 1 {
            return self.cert_id.clone();
        }
        let offset = index - 2;
        if offset < N_LIMBS {
            return self.scalar.limbs()[offset].clone();
        }
        if offset < 2 * N_LIMBS {
            return self.base_x.limbs()[offset - N_LIMBS].clone();
        }
        if offset < 3 * N_LIMBS {
            return self.base_y.limbs()[offset - 2 * N_LIMBS].clone();
        }
        match offset - 3 * N_LIMBS {
            0 => self.base_inf.clone(),
            1 => self.scalar_is_zero.clone(),
            2 => self.scalar_is_nonzero.clone(),
            3 => self.cert_active.clone(),
            4 => self.cert_zero_active.clone(),
            _ => panic!("cert scalar input relation index {index} out of range"),
        }
    }

    fn values(&self) -> Vec<F> {
        let mut values = Vec::with_capacity(CERT_SCALAR_INPUT_ROW_COLUMNS);
        values.push(self.sig_id.clone());
        values.push(self.cert_id.clone());
        values.extend(self.scalar.limbs().iter().cloned());
        values.extend(self.base_x.limbs().iter().cloned());
        values.extend(self.base_y.limbs().iter().cloned());
        values.push(self.base_inf.clone());
        values.push(self.scalar_is_zero.clone());
        values.push(self.scalar_is_nonzero.clone());
        values.push(self.cert_active.clone());
        values.push(self.cert_zero_active.clone());
        values
    }
}

impl<F> CertScalarInputAirRow<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            sig_id: eval.next_trace_mask(),
            cert_id: eval.next_trace_mask(),
            scalar: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
            base_x: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
            base_y: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
            base_inf: eval.next_trace_mask(),
            scalar_is_zero: eval.next_trace_mask(),
            scalar_is_nonzero: eval.next_trace_mask(),
            cert_active: eval.next_trace_mask(),
            cert_zero_active: eval.next_trace_mask(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateScalarSource {
    U1Generator,
    U2PublicKey,
}

impl CertificateScalarSource {
    pub const fn cert_id(self) -> u32 {
        match self {
            Self::U1Generator => CERT_ID_U1_GENERATOR,
            Self::U2PublicKey => CERT_ID_U2_PUBLIC_KEY,
        }
    }

    fn base_x(self, output: &ScalarSetupOutput<M31>) -> P256M31BigInt {
        match self {
            Self::U1Generator => P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_GX)),
            Self::U2PublicKey => output.pub_x.clone(),
        }
    }

    fn base_y(self, output: &ScalarSetupOutput<M31>) -> P256M31BigInt {
        match self {
            Self::U1Generator => P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_GY)),
            Self::U2PublicKey => output.pub_y.clone(),
        }
    }
}

pub fn gen_cert_scalar_input_air_base_trace(
    scalar_setup: &ScalarSetupClaim,
    certs: &CertScalarInputClaim,
    proof_claim: CertScalarInputAirProofClaim,
) -> ColumnVec<M31ColumnEval> {
    let row_count = 1usize << proof_claim.log_size;
    assert!(scalar_setup.rows.len() <= row_count);
    assert_eq!(certs.rows.len(), 2 * scalar_setup.rows.len());
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); row_count]; CERT_SCALAR_INPUT_TRACE_COLUMNS];
    for (row_index, setup_row) in scalar_setup.rows.iter().enumerate() {
        let cert0 = &certs.rows[2 * row_index];
        let cert1 = &certs.rows[2 * row_index + 1];
        let mut offset = 0usize;
        columns[offset][row_index] = M31::from_u32_unchecked(1);
        offset += 1;
        for value in setup_row.output.relation_values() {
            columns[offset][row_index] = value;
            offset += 1;
        }
        write_cert_row(&mut columns, &mut offset, cert0, row_index);
        write_cert_row(&mut columns, &mut offset, cert1, row_index);
        columns[offset][row_index] = nonzero_inverse_or_zero(cert0.scalar.limbs());
        offset += 1;
        columns[offset][row_index] = nonzero_inverse_or_zero(cert1.scalar.limbs());
        offset += 1;
        debug_assert_eq!(offset, CERT_SCALAR_INPUT_TRACE_COLUMNS);
    }
    columns
        .into_iter()
        .map(|values| m31_column_eval(proof_claim.log_size, values))
        .collect()
}

pub(crate) fn gen_cert_scalar_input_air_interaction_trace(
    base: &[M31ColumnEval],
    setup_relation: &ScalarSetupOutputRelation,
    cert_relation: &CertScalarInputRelation,
    cert_base_relation: Option<&CertBaseRelation>,
) -> (ColumnVec<M31ColumnEval>, CertScalarInputAirInteractionClaim) {
    assert_eq!(base.len(), CERT_SCALAR_INPUT_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = scalar_setup_output_packed_values_from_cert_base(base, vec_row);
        col.write_frac(
            vec_row,
            PackedQM31::from(base[0].data[vec_row]),
            setup_relation.combine(&values),
        );
    }
    col.finalize_col();
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            -PackedQM31::from(base[0].data[vec_row]),
            cert_relation.combine(&cert_packed_values_from_base(base, vec_row, cert0_col())),
        );
    }
    col.finalize_col();
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            -PackedQM31::from(base[0].data[vec_row]),
            cert_relation.combine(&cert_packed_values_from_base(base, vec_row, cert1_col())),
        );
    }
    col.finalize_col();
    // CertBase providers (yield `-count·cert_active`), one column per cert. Only
    // emitted when the prepared-table consumer exists (monolithic STARK), in
    // lockstep with `CertScalarInputAirEval`'s two extra `add_to_relation` calls.
    if let Some(cert_base_relation) = cert_base_relation {
        for (cert_col, count) in [
            (cert0_col(), CERT0_PREPARED_P_CELL_COUNT),
            (cert1_col(), CERT1_PREPARED_P_CELL_COUNT),
        ] {
            let count_packed = PackedM31::broadcast(M31::from_u32_unchecked(count));
            let mut col = logup.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                let cert_active = base[cert_col + CERT_ACTIVE_ROW_OFFSET].data[vec_row];
                let numerator = -PackedQM31::from(count_packed * cert_active);
                col.write_frac(
                    vec_row,
                    numerator,
                    cert_base_relation
                        .combine(&cert_base_packed_values_from_base(base, vec_row, cert_col)),
                );
            }
            col.finalize_col();
        }
    }
    let (trace, claimed_sum) = logup.finalize_last();
    let scalar_setup_consumer_claimed_sum: SecureField = storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .map(|row| {
            let values = scalar_setup_output_values_from_cert_base(&row);
            let denominator: SecureField = setup_relation.combine(&values);
            SecureField::from(row[0]) / denominator
        })
        .sum();
    let cert_provider_claimed_sum: SecureField = storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .flat_map(|row| {
            [
                cert_values_from_base(&row, cert0_col()),
                cert_values_from_base(&row, cert1_col()),
            ]
        })
        .map(|values| -> SecureField {
            let denominator: SecureField = cert_relation.combine(&values);
            -SecureField::from(M31::from_u32_unchecked(1)) / denominator
        })
        .sum();
    let cert_base_provider_claimed_sum: SecureField = match cert_base_relation {
        None => secure_zero(),
        Some(cert_base_relation) => storage_rows(base)
            .filter(|row| row[0] != M31::from_u32_unchecked(0))
            .flat_map(|row| {
                [
                    (cert0_col(), CERT0_PREPARED_P_CELL_COUNT),
                    (cert1_col(), CERT1_PREPARED_P_CELL_COUNT),
                ]
                .map(|(cert_col, count)| (row.clone(), cert_col, count))
            })
            .map(|(row, cert_col, count)| -> SecureField {
                let cert_active = row[cert_col + CERT_ACTIVE_ROW_OFFSET];
                let numerator = M31::from_u32_unchecked(count) * cert_active;
                let values = cert_base_values_from_base(&row, cert_col);
                let denominator: SecureField = cert_base_relation.combine(&values);
                -SecureField::from(numerator) / denominator
            })
            .sum(),
    };
    (
        trace,
        CertScalarInputAirInteractionClaim {
            claimed_sum,
            scalar_setup_consumer_claimed_sum,
            cert_provider_claimed_sum,
            cert_base_provider_claimed_sum,
        },
    )
}

/// Build the `CertBaseRelation` tuple `(sig_id, cert_id, base_x[..], base_y[..])`
/// from a cert row.
fn cert_base_relation_values_from_row<F: Clone>(
    row: &CertScalarInputAirRow<F>,
) -> [F; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => row.sig_id.clone(),
        1 => row.cert_id.clone(),
        2..=21 => row.base_x.limbs()[index - 2].clone(),
        22..=41 => row.base_y.limbs()[index - 2 - N_LIMBS].clone(),
        _ => unreachable!("cert base relation index in range"),
    })
}

fn read_scalar_setup_output<E: EvalAtRow>(eval: &mut E) -> ScalarSetupOutput<E::F> {
    ScalarSetupOutput {
        sig_id: eval.next_trace_mask(),
        u1: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        u2: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        r: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        pub_x: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
        pub_y: P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask())),
    }
}

fn read_cert_scalar_input_air_row<E: EvalAtRow>(eval: &mut E) -> CertScalarInputAirRow<E::F> {
    CertScalarInputAirRow::read(eval)
}

fn constrain_cert_from_setup<E: EvalAtRow>(
    eval: &mut E,
    active: E::F,
    setup: &ScalarSetupOutput<E::F>,
    cert: &CertScalarInputAirRow<E::F>,
    source: CertificateScalarSource,
    nonzero_inv: E::F,
) {
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let one = E::F::from(M31::from_u32_unchecked(1));
    eval.add_constraint(active.clone() * (cert.sig_id.clone() - setup.sig_id.clone()));
    eval.add_constraint(
        active.clone()
            * (cert.cert_id.clone() - E::F::from(M31::from_u32_unchecked(source.cert_id()))),
    );
    for limb in 0..N_LIMBS {
        let expected_scalar = match source {
            CertificateScalarSource::U1Generator => setup.u1.limbs()[limb].clone(),
            CertificateScalarSource::U2PublicKey => setup.u2.limbs()[limb].clone(),
        };
        let expected_x = match source {
            CertificateScalarSource::U1Generator => fixed_generator_limb::<E>(true, limb),
            CertificateScalarSource::U2PublicKey => setup.pub_x.limbs()[limb].clone(),
        };
        let expected_y = match source {
            CertificateScalarSource::U1Generator => fixed_generator_limb::<E>(false, limb),
            CertificateScalarSource::U2PublicKey => setup.pub_y.limbs()[limb].clone(),
        };
        eval.add_constraint(active.clone() * (cert.scalar.limbs()[limb].clone() - expected_scalar));
        eval.add_constraint(active.clone() * (cert.base_x.limbs()[limb].clone() - expected_x));
        eval.add_constraint(active.clone() * (cert.base_y.limbs()[limb].clone() - expected_y));
        eval.add_constraint(cert.scalar_is_zero.clone() * cert.scalar.limbs()[limb].clone());
    }
    eval.add_constraint(active.clone() * cert.base_inf.clone());
    for flag in [
        cert.scalar_is_zero.clone(),
        cert.scalar_is_nonzero.clone(),
        cert.cert_active.clone(),
        cert.cert_zero_active.clone(),
    ] {
        eval.add_constraint(flag.clone() * (flag - one.clone()));
    }
    eval.add_constraint(
        cert.scalar_is_zero.clone() + cert.scalar_is_nonzero.clone() - active.clone(),
    );
    eval.add_constraint(cert.cert_active.clone() - cert.scalar_is_nonzero.clone());
    eval.add_constraint(cert.cert_zero_active.clone() - cert.scalar_is_zero.clone());
    let scalar_sum = cert
        .scalar
        .limbs()
        .iter()
        .cloned()
        .fold(zero, |acc, limb| acc + limb);
    eval.add_constraint(cert.scalar_is_nonzero.clone() * (scalar_sum * nonzero_inv - one.clone()));
    if source == CertificateScalarSource::U2PublicKey {
        eval.add_constraint(active.clone() * (cert.scalar_is_nonzero.clone() - one));
        eval.add_constraint(active * cert.scalar_is_zero.clone());
    }
}

fn constrain_cert_padding<E: EvalAtRow>(
    eval: &mut E,
    active: E::F,
    cert: &CertScalarInputAirRow<E::F>,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    for value in cert.values() {
        eval.add_constraint((one.clone() - active.clone()) * value);
    }
}

fn fixed_generator_limb<E: EvalAtRow>(x_coordinate: bool, limb: usize) -> E::F {
    let point = if x_coordinate { &P256_GX } else { &P256_GY };
    let limbs = P256M31BigInt::from_u256(&U256::from_le_u64s(point));
    E::F::from(limbs.limbs()[limb])
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertScalarInputError {
    FlagMismatch {
        field: &'static str,
        expected: u32,
        actual: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    UnexpectedZeroU2 {
        sig_id: u32,
    },
}

impl fmt::Display for CertScalarInputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FlagMismatch {
                field,
                expected,
                actual,
            } => write!(
                f,
                "certificate scalar input mismatch for {field}: expected {expected}, got {actual}"
            ),
            Self::NonBooleanFlag { field, actual } => {
                write!(
                    f,
                    "certificate scalar input flag {field} must be boolean, got {actual}"
                )
            }
            Self::UnexpectedZeroU2 { sig_id } => {
                write!(f, "signature {sig_id} has an unexpected zero u2 scalar")
            }
        }
    }
}

impl std::error::Error for CertScalarInputError {}

fn is_zero_bigint(value: &P256M31BigInt) -> bool {
    value.limbs().iter().all(|limb| limb.0 == 0)
}

fn write_cert_row(
    columns: &mut [Vec<M31>],
    offset: &mut usize,
    row: &CertScalarInputRow,
    row_index: usize,
) {
    columns[*offset][row_index] = row.sig_id;
    *offset += 1;
    columns[*offset][row_index] = row.cert_id;
    *offset += 1;
    for value in row.scalar.limbs() {
        columns[*offset][row_index] = *value;
        *offset += 1;
    }
    for value in row.base_x.limbs() {
        columns[*offset][row_index] = *value;
        *offset += 1;
    }
    for value in row.base_y.limbs() {
        columns[*offset][row_index] = *value;
        *offset += 1;
    }
    columns[*offset][row_index] = row.base_inf;
    *offset += 1;
    columns[*offset][row_index] = row.scalar_is_zero;
    *offset += 1;
    columns[*offset][row_index] = row.scalar_is_nonzero;
    *offset += 1;
    columns[*offset][row_index] = row.cert_active;
    *offset += 1;
    columns[*offset][row_index] = row.cert_zero_active;
    *offset += 1;
}

fn nonzero_inverse_or_zero(limbs: &[M31; N_LIMBS]) -> M31 {
    let sum = limbs.iter().fold(0u64, |acc, limb| acc + u64::from(limb.0));
    if sum == 0 {
        M31::from_u32_unchecked(0)
    } else {
        m31_inverse(M31::from_u32_unchecked(sum as u32))
    }
}

fn m31_inverse(value: M31) -> M31 {
    const MODULUS: u64 = (1u64 << 31) - 1;
    let mut base = u64::from(value.0);
    let mut exp = MODULUS - 2;
    let mut acc = 1u64;
    while exp != 0 {
        if exp & 1 == 1 {
            acc = (acc * base) % MODULUS;
        }
        base = (base * base) % MODULUS;
        exp >>= 1;
    }
    M31::from_u32_unchecked(acc as u32)
}

fn scalar_setup_output_packed_values_from_cert_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; SCALAR_SETUP_OUTPUT_ARITY] {
    core::array::from_fn(|index| base[1 + index].data[vec_row])
}

fn scalar_setup_output_values_from_cert_base(row: &[M31]) -> [M31; SCALAR_SETUP_OUTPUT_ARITY] {
    core::array::from_fn(|index| row[1 + index])
}

fn cert_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
    start: usize,
) -> [PackedM31; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|index| base[start + index].data[vec_row])
}

fn cert_values_from_base(row: &[M31], start: usize) -> [M31; CERT_SCALAR_INPUT_RELATION_ARITY] {
    core::array::from_fn(|index| row[start + index])
}

/// Column offset (within a cert row block) of `cert_active`: after `sig_id`,
/// `cert_id`, the three `N_LIMBS` bigints (`scalar`, `base_x`, `base_y`),
/// `base_inf`, `scalar_is_zero`, and `scalar_is_nonzero`.
const CERT_ACTIVE_ROW_OFFSET: usize = 2 + 3 * N_LIMBS + 1 + 2;

/// `CertBaseRelation` tuple from a cert row block: `(sig_id, cert_id, base_x[..],
/// base_y[..])`. Mirrors `cert_base_relation_values_from_row`.
fn cert_base_index_in_row(index: usize) -> usize {
    match index {
        0 => 0,                                // sig_id
        1 => 1,                                // cert_id
        2..=21 => 2 + N_LIMBS + (index - 2),   // base_x limbs
        22..=41 => 2 + 2 * N_LIMBS + (index - 22), // base_y limbs
        _ => unreachable!("cert base relation index in range"),
    }
}

fn cert_base_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
    start: usize,
) -> [PackedM31; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| base[start + cert_base_index_in_row(index)].data[vec_row])
}

fn cert_base_values_from_base(row: &[M31], start: usize) -> [M31; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| row[start + cert_base_index_in_row(index)])
}

const fn cert0_col() -> usize {
    1 + SCALAR_SETUP_OUTPUT_ARITY
}

const fn cert1_col() -> usize {
    cert0_col() + CERT_SCALAR_INPUT_ROW_COLUMNS
}

fn storage_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count).map(|row| {
        let vec_row = row / (1 << LOG_N_LANES);
        let lane = row % (1 << LOG_N_LANES);
        base.iter()
            .map(|column| column.data[vec_row].to_array()[lane])
            .collect::<Vec<_>>()
    })
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

fn m31_bool(value: bool) -> M31 {
    M31::from_u32_unchecked(u32::from(value))
}

fn require_bool(field: &'static str, value: M31) -> Result<(), CertScalarInputError> {
    if value.0 <= 1 {
        return Ok(());
    }
    Err(CertScalarInputError::NonBooleanFlag {
        field,
        actual: value.0,
    })
}

fn require_eq(field: &'static str, actual: u32, expected: u32) -> Result<(), CertScalarInputError> {
    if actual == expected {
        return Ok(());
    }
    Err(CertScalarInputError::FlagMismatch {
        field,
        expected,
        actual,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::{
        public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
    };
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature};
    use stwo::core::fields::qm31::SecureField;

    fn test_input(message_hash: U256, r: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash,
            signature: Signature {
                r: scalar(r),
                s: scalar(11),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    #[test]
    fn cert_scalar_claim_binds_two_certificates_per_signature() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");

        assert_eq!(certs.rows.len(), 2);
        assert_eq!(certs.rows[0].cert_id.0, CERT_ID_U1_GENERATOR);
        assert_eq!(certs.rows[0].scalar, scalar_setup.rows[0].output.u1);
        assert_eq!(
            certs.rows[0].base_x,
            P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_GX))
        );
        assert_eq!(certs.rows[1].cert_id.0, CERT_ID_U2_PUBLIC_KEY);
        assert_eq!(certs.rows[1].scalar, scalar_setup.rows[0].output.u2);
        assert_eq!(certs.rows[1].base_x, scalar_setup.rows[0].output.pub_x);
    }

    #[test]
    fn cert_scalar_claim_allows_u1_zero_branch() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(U256::ZERO, 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");

        assert_eq!(certs.rows[0].cert_id.0, CERT_ID_U1_GENERATOR);
        assert_eq!(certs.rows[0].scalar_is_zero.0, 1);
        assert_eq!(certs.rows[0].cert_zero_active.0, 1);
        assert_eq!(certs.rows[0].cert_active.0, 0);
        assert_eq!(certs.rows[1].cert_id.0, CERT_ID_U2_PUBLIC_KEY);
        assert_eq!(certs.rows[1].scalar_is_nonzero.0, 1);
    }

    #[test]
    fn cert_scalar_e2e_keeps_public_logup_balanced() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        scalar_setup.verify().expect("scalar setup verifies");
        certs.verify().expect("cert inputs verify");
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn cert_scalar_claim_rejects_mutated_zero_flag() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let mut certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        certs.rows[0].scalar_is_zero = M31::from_u32_unchecked(1);

        let err = certs.verify().expect_err("mutated zero flag must fail");

        assert!(matches!(err, CertScalarInputError::FlagMismatch { .. }));
    }

    #[test]
    fn cert_scalar_claim_rejects_zero_u2() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(U256::ZERO, 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let mut certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        certs.rows[1].scalar = P256M31BigInt::zero();
        certs.rows[1].scalar_is_zero = M31::from_u32_unchecked(1);
        certs.rows[1].scalar_is_nonzero = M31::from_u32_unchecked(0);
        certs.rows[1].cert_active = M31::from_u32_unchecked(0);
        certs.rows[1].cert_zero_active = M31::from_u32_unchecked(1);

        let err = certs.verify().expect_err("zero u2 must fail");

        assert!(matches!(err, CertScalarInputError::UnexpectedZeroU2 { .. }));
    }

    #[test]
    fn cert_scalar_claim_mixes_into_transcript() {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(scalar(42), 77)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let mut channel = stwo::core::channel::Blake2sM31Channel::default();

        certs.mix_into(&mut channel);
    }
}
