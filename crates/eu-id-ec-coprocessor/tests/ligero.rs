use eu_id_ec_coprocessor::ligero::{
    commit_witness, v1_ligero_params, verify_input_claims_from_systematic_openings,
    verify_openings, LigeroParams,
};
use eu_id_ec_coprocessor::merkle::{commit_columns, verify_column, ColumnOpening};
use eu_id_ec_coprocessor::rs::{is_codeword, rs_encode};
use eu_id_ec_coprocessor::sumcheck::InputClaims;
use eu_id_ec_coprocessor::{Circuit, CoprocessorChannel, Fp, Layer, Mle, QuadTerm};

fn term(out: u32, l: u32, r: u32, coeff: u64) -> QuadTerm {
    QuadTerm {
        out,
        l,
        r,
        coeff: Fp::from_u64(coeff),
    }
}

#[test]
fn rs_encoding_preserves_message_prefix() {
    let row = (0u64..8).map(Fp::from_u64).collect::<Vec<_>>();
    let encoded = rs_encode(&row, 16).unwrap();

    assert_eq!(&encoded[..row.len()], row.as_slice());
    assert!(is_codeword(&encoded, row.len()).unwrap());
}

#[test]
fn rs_encoding_matches_known_quadratic_values() {
    let row = (0u64..4)
        .map(|x| Fp::from_u64(x * x + 2 * x + 3))
        .collect::<Vec<_>>();
    let encoded = rs_encode(&row, 8).unwrap();

    for x in 0u64..8 {
        assert_eq!(encoded[x as usize], Fp::from_u64(x * x + 2 * x + 3));
    }
}

#[test]
fn corrupt_rs_symbol_rejects_codeword_check() {
    let row = (10u64..18).map(Fp::from_u64).collect::<Vec<_>>();
    let mut encoded = rs_encode(&row, 16).unwrap();
    encoded[12] = encoded[12] + Fp::ONE;

    assert!(!is_codeword(&encoded, row.len()).unwrap());
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
    let params = LigeroParams {
        row_len: 4,
        degree_bound: 7,
        codeword_len: 16,
        openings: 3,
        proximity_radius: 0,
    };
    let values = (1u64..=10).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let indices = [0usize, 3, 7];
    let openings = commitment.open_columns(&indices).unwrap();
    let gamma = [Fp::from_u64(2), Fp::from_u64(3), Fp::from_u64(5)];
    let claim = commitment.proximity_claim(&gamma).unwrap();

    assert!(verify_openings(commitment.root(), params, &openings, &claim, &gamma).unwrap());
}

#[test]
fn ligero_proximity_claim_sends_message_row_not_full_codeword() {
    let params = LigeroParams {
        row_len: 4,
        degree_bound: 7,
        codeword_len: 16,
        openings: 3,
        proximity_radius: 0,
    };
    let values = (1u64..=10).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let gamma = [Fp::from_u64(2), Fp::from_u64(3), Fp::from_u64(5)];
    let claim = commitment.proximity_claim(&gamma).unwrap();

    assert_eq!(claim.combined_row.len(), params.degree_bound);
}

#[test]
fn ligero_opening_verifier_rejects_corrupt_combined_row() {
    let params = LigeroParams {
        row_len: 4,
        degree_bound: 6,
        codeword_len: 16,
        openings: 2,
        proximity_radius: 0,
    };
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let openings = commitment.open_columns(&[1usize, 6]).unwrap();
    let gamma = [Fp::from_u64(7), Fp::from_u64(11)];
    let mut claim = commitment.proximity_claim(&gamma).unwrap();
    claim.combined_row[0] = claim.combined_row[0] + Fp::ONE;

    assert!(!verify_openings(commitment.root(), params, &openings, &claim, &gamma).unwrap());
}

#[test]
fn systematic_openings_verify_bl2_input_claims_against_committed_witness() {
    let params = LigeroParams {
        row_len: 4,
        degree_bound: 4,
        codeword_len: 16,
        openings: 0,
        proximity_radius: 0,
    };
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let openings = commitment.open_systematic_columns().unwrap();
    let mle = Mle::new(values);
    let claims = InputClaims {
        points: [
            vec![Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)],
            vec![Fp::from_u64(11), Fp::from_u64(13), Fp::from_u64(17)],
        ],
        values: [
            mle.eval_at(&[Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)])
                .unwrap(),
            mle.eval_at(&[Fp::from_u64(11), Fp::from_u64(13), Fp::from_u64(17)])
                .unwrap(),
        ],
    };

    assert!(verify_input_claims_from_systematic_openings(
        commitment.root(),
        params,
        &openings,
        &claims,
    )
    .unwrap());
}

#[test]
fn systematic_openings_accept_bl2_sumcheck_input_claims() {
    let circuit = Circuit::new(vec![Layer::new(
        1,
        2,
        vec![term(0, 0, 1, 1), term(1, 2, 3, 1)],
    )
    .unwrap()])
    .unwrap();
    let input_layer = vec![Fp::ZERO, Fp::from_u64(7), Fp::ZERO, Fp::from_u64(11)];
    let witness = circuit.evaluate_input(input_layer.clone()).unwrap();
    let params = LigeroParams {
        row_len: 2,
        degree_bound: 2,
        codeword_len: 8,
        openings: 0,
        proximity_radius: 0,
    };
    let commitment = commit_witness(&input_layer, params).unwrap();
    let mut prover_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    let proof = eu_id_ec_coprocessor::sumcheck::prove_circuit(
        &circuit,
        &witness,
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

    assert!(verify_input_claims_from_systematic_openings(
        commitment.root(),
        params,
        &commitment.open_systematic_columns().unwrap(),
        &claims,
    )
    .unwrap());
}

#[test]
fn systematic_openings_reject_bad_input_claim_and_corrupt_column() {
    let params = LigeroParams {
        row_len: 4,
        degree_bound: 4,
        codeword_len: 16,
        openings: 0,
        proximity_radius: 0,
    };
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values.clone(), params).unwrap();
    let openings = commitment.open_systematic_columns().unwrap();
    let mle = Mle::new(values);
    let mut claims = InputClaims {
        points: [
            vec![Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)],
            vec![Fp::from_u64(11), Fp::from_u64(13), Fp::from_u64(17)],
        ],
        values: [
            mle.eval_at(&[Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7)])
                .unwrap(),
            mle.eval_at(&[Fp::from_u64(11), Fp::from_u64(13), Fp::from_u64(17)])
                .unwrap(),
        ],
    };
    claims.values[0] = claims.values[0] + Fp::ONE;
    assert!(!verify_input_claims_from_systematic_openings(
        commitment.root(),
        params,
        &openings,
        &claims,
    )
    .unwrap());

    let mut corrupt_openings = openings;
    corrupt_openings[0].column[0] = corrupt_openings[0].column[0] + Fp::ONE;
    assert!(!verify_input_claims_from_systematic_openings(
        commitment.root(),
        params,
        &corrupt_openings,
        &claims,
    )
    .unwrap());
}

#[test]
fn pinned_v1_ligero_params_meet_q027_non_zk_soundness_bounds() {
    let params = v1_ligero_params();

    assert_eq!(params.row_len, 64);
    assert_eq!(params.degree_bound, 64);
    assert_eq!(params.codeword_len, 512);
    assert_eq!(params.openings, 160);
    assert_eq!(params.proximity_radius, 223);
    params.validate().unwrap();
    assert!(params.degree_bound >= params.row_len);
    assert!(params.openings >= 156);
    assert!(params.soundness_error() <= 2f64.powi(-128));
}
