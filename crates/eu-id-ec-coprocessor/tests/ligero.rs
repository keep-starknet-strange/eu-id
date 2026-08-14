use eu_id_ec_coprocessor::circle_fft::{
    circle_encode, circle_evaluate, circle_ifft_codeword, PRODUCT_CIRCLE_GEOM,
};
use eu_id_ec_coprocessor::ligero::{
    commit_witness, product_circle_params, verify_claim_batch, verify_openings, LigeroLinearClaim,
    LigeroParams, LIGERO_AUXILIARY_ROW_COUNT,
};
use eu_id_ec_coprocessor::merkle::{commit_columns, verify_column, ColumnOpening};
use eu_id_ec_coprocessor::sumcheck::CircuitPads;
use eu_id_ec_coprocessor::{Circuit, CoprocessorChannel, Fp, Layer, Mle, QuadTerm};

fn term(out: u32, l: u32, r: u32, coeff: u64) -> QuadTerm {
    QuadTerm {
        out,
        l,
        r,
        coeff: Fp::from_u64(coeff),
    }
}

fn opening_indices(params: LigeroParams) -> Vec<usize> {
    (0..params.openings)
        .map(|index| (index * 19 + 3) % params.codeword_len)
        .collect()
}

#[test]
fn circle_encoding_round_trips_coefficients() {
    let row = (0u64..8).map(Fp::from_u64).collect::<Vec<_>>();
    let encoded = circle_encode(PRODUCT_CIRCLE_GEOM, &row, row.len()).unwrap();
    let recovered = circle_ifft_codeword(PRODUCT_CIRCLE_GEOM, encoded).unwrap();

    assert_eq!(&recovered[..row.len()], row.as_slice());
    assert!(recovered[row.len()..]
        .iter()
        .all(|&value| value == Fp::ZERO));
}

#[test]
fn circle_encoding_matches_independent_point_evaluation() {
    let row = (0u64..4)
        .map(|x| Fp::from_u64(x * x + 2 * x + 3))
        .collect::<Vec<_>>();
    let encoded = circle_encode(PRODUCT_CIRCLE_GEOM, &row, row.len()).unwrap();

    for index in [0, 1, 17, 257, 4095] {
        assert_eq!(
            encoded[index],
            circle_evaluate(PRODUCT_CIRCLE_GEOM, &row, index).unwrap()
        );
    }
}

#[test]
fn corrupt_circle_symbol_rejects_degree_bound_check() {
    let row = (10u64..18).map(Fp::from_u64).collect::<Vec<_>>();
    let mut encoded = circle_encode(PRODUCT_CIRCLE_GEOM, &row, row.len()).unwrap();
    encoded[12] = encoded[12] + Fp::ONE;
    let recovered = circle_ifft_codeword(PRODUCT_CIRCLE_GEOM, encoded).unwrap();

    assert!(recovered[row.len()..]
        .iter()
        .any(|&value| value != Fp::ZERO));
}

#[test]
fn merkle_column_opening_accepts_and_corruption_rejects() {
    let rows = vec![
        vec![
            Fp::from_u64(1),
            Fp::from_u64(2),
            Fp::from_u64(3),
            Fp::from_u64(4),
        ],
        vec![
            Fp::from_u64(5),
            Fp::from_u64(6),
            Fp::from_u64(7),
            Fp::from_u64(8),
        ],
    ];
    let commitment = commit_columns(&rows).unwrap();
    let opening = commitment.open(2).unwrap();

    assert!(verify_column(commitment.root(), &opening).unwrap());

    let mut corrupted = ColumnOpening {
        column: opening.column.clone(),
        index: opening.index,
        path: opening.path.clone(),
    };
    corrupted.column[0] = corrupted.column[0] + Fp::ONE;
    assert!(!verify_column(commitment.root(), &corrupted).unwrap());
}

#[test]
fn ligero_commit_open_verify_accepts_known_columns() {
    let params = product_circle_params();
    let values = (1u64..=10).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let indices = opening_indices(params);
    let openings = commitment.open_columns(&indices).unwrap();
    assert_eq!(openings[0].column.len(), 1 + LIGERO_AUXILIARY_ROW_COUNT);
    let gamma = [Fp::from_u64(2)];
    let claim = commitment.proximity_claim(&gamma).unwrap();

    assert!(verify_openings(commitment.root(), params, &openings, &claim, &gamma).unwrap());
}

#[test]
fn ligero_proximity_claim_sends_message_row_not_full_codeword() {
    let params = product_circle_params();
    let values = (1u64..=10).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let gamma = [Fp::from_u64(2)];
    let claim = commitment.proximity_claim(&gamma).unwrap();

    assert_eq!(claim.combined_row.len(), params.degree_bound);
}

#[test]
fn ligero_opening_verifier_rejects_corrupt_combined_row() {
    let params = product_circle_params();
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let openings = commitment.open_columns(&opening_indices(params)).unwrap();
    let gamma = [Fp::from_u64(7)];
    let mut claim = commitment.proximity_claim(&gamma).unwrap();
    claim.combined_row[0] = claim.combined_row[0] + Fp::ONE;

    assert!(!verify_openings(commitment.root(), params, &openings, &claim, &gamma).unwrap());
}

#[test]
fn ligero_proximity_claim_is_masked_for_same_witness() {
    let params = product_circle_params();
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let gamma = [Fp::from_u64(7)];
    let indices = opening_indices(params);

    let first = commit_witness(&values, params).unwrap();
    let second = commit_witness(&values, params).unwrap();
    let first_claim = first.proximity_claim(&gamma).unwrap();
    let second_claim = second.proximity_claim(&gamma).unwrap();

    assert_ne!(first.root(), second.root());
    assert_ne!(first_claim.combined_row, second_claim.combined_row);
    assert!(verify_openings(
        first.root(),
        params,
        &first.open_columns(&indices).unwrap(),
        &first_claim,
        &gamma
    )
    .unwrap());
    assert!(verify_openings(
        second.root(),
        params,
        &second.open_columns(&indices).unwrap(),
        &second_claim,
        &gamma
    )
    .unwrap());
}

#[test]
fn circle_claim_batch_verifies_mle_claims_against_committed_witness() {
    let params = product_circle_params();
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let openings = commitment.open_columns(&opening_indices(params)).unwrap();
    let mle = Mle::new(values.clone());
    let claims = [
        vec![Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)],
        vec![Fp::from_u64(11), Fp::from_u64(13), Fp::from_u64(17)],
    ]
    .map(|point| {
        let value = mle.eval_at(&point).unwrap();
        LigeroLinearClaim::mle(0, values.len(), point, value)
    });
    let gamma = [Fp::from_u64(19), Fp::from_u64(23)];
    let batch = commitment.claim_batch(&claims, &gamma).unwrap();

    assert!(verify_claim_batch(
        commitment.root(),
        params,
        values.len(),
        &openings,
        &batch,
        &claims,
        &gamma,
    )
    .unwrap());
}

#[test]
fn circle_claim_batch_does_not_treat_masked_sumcheck_claims_as_raw_witness_claims() {
    let circuit = Circuit::new(vec![Layer::new(
        1,
        2,
        vec![term(0, 0, 1, 1), term(1, 2, 3, 1)],
    )
    .unwrap()])
    .unwrap();
    let input_layer = vec![Fp::ZERO, Fp::from_u64(7), Fp::ZERO, Fp::from_u64(11)];
    let witness = circuit.evaluate_input(input_layer.clone()).unwrap();
    let params = product_circle_params();
    let commitment = commit_witness(&input_layer, params).unwrap();
    let pads = CircuitPads::fresh(&circuit);
    let mut prover_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    let proof = eu_id_ec_coprocessor::sumcheck::prove_circuit(
        &circuit,
        &witness,
        &pads,
        commitment.root(),
        &mut prover_channel,
    )
    .unwrap();
    let mut verifier_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    let claims = eu_id_ec_coprocessor::sumcheck::verify_circuit(
        &circuit,
        &proof,
        commitment.root(),
        &mut verifier_channel,
    )
    .unwrap();

    let raw_mle = Mle::new(input_layer.clone());
    assert!(
        claims
            .input_claims
            .points
            .iter()
            .zip(claims.input_claims.values)
            .any(|(point, masked)| raw_mle.eval_at(point).unwrap() != masked),
        "sumcheck input claims must remain masked instead of exposing raw witness evaluations"
    );
    let direct_claims = claims
        .input_claims
        .points
        .iter()
        .cloned()
        .zip(claims.input_claims.values)
        .map(|(point, value)| LigeroLinearClaim::mle(0, input_layer.len(), point, value))
        .collect::<Vec<_>>();
    let gamma = [Fp::from_u64(19), Fp::from_u64(23)];
    let batch = commitment.claim_batch(&direct_claims, &gamma).unwrap();
    assert!(!verify_claim_batch(
        commitment.root(),
        params,
        input_layer.len(),
        &commitment.open_columns(&opening_indices(params)).unwrap(),
        &batch,
        &direct_claims,
        &gamma,
    )
    .unwrap());
}

#[test]
fn circle_claim_batch_rejects_bad_input_claim_and_corrupt_column() {
    let params = product_circle_params();
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let mut openings = commitment.open_columns(&opening_indices(params)).unwrap();
    let point = vec![Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)];
    let value = Mle::new(values.clone()).eval_at(&point).unwrap();
    let claims = [LigeroLinearClaim::mle(0, values.len(), point, value)];
    let gamma = [Fp::from_u64(19)];
    let batch = commitment.claim_batch(&claims, &gamma).unwrap();

    let mut bad_claims = claims.clone();
    bad_claims[0].value = bad_claims[0].value + Fp::ONE;
    assert!(!verify_claim_batch(
        commitment.root(),
        params,
        values.len(),
        &openings,
        &batch,
        &bad_claims,
        &gamma,
    )
    .unwrap());

    openings[0].column[0] = openings[0].column[0] + Fp::ONE;
    assert!(!verify_claim_batch(
        commitment.root(),
        params,
        values.len(),
        &openings,
        &batch,
        &claims,
        &gamma,
    )
    .unwrap());
}
