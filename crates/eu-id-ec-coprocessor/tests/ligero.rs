use eu_id_ec_coprocessor::ligero::{
    commit_witness, v1_ligero_params, v2_ligero_params, v2_ligero_params_b,
    verify_input_claims_from_systematic_openings_with_len, verify_openings, LigeroCode,
    LigeroParams,
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
        code: LigeroCode::Rs,
    };
    let values = (1u64..=10).map(Fp::from_u64).collect::<Vec<_>>();
    let commitment = commit_witness(&values, params).unwrap();
    let indices = [0usize, 3, 7];
    let openings = commitment.open_columns(&indices).unwrap();
    assert_eq!(openings[0].column.len(), 5);
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
        code: LigeroCode::Rs,
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
        code: LigeroCode::Rs,
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
fn ligero_proximity_claim_is_masked_for_same_witness() {
    let params = LigeroParams {
        row_len: 4,
        degree_bound: 7,
        codeword_len: 16,
        openings: 2,
        proximity_radius: 0,
        code: LigeroCode::Rs,
    };
    let values = (1u64..=8).map(Fp::from_u64).collect::<Vec<_>>();
    let gamma = [Fp::from_u64(7), Fp::from_u64(11)];

    let first = commit_witness(&values, params).unwrap();
    let second = commit_witness(&values, params).unwrap();
    let first_claim = first.proximity_claim(&gamma).unwrap();
    let second_claim = second.proximity_claim(&gamma).unwrap();

    assert_ne!(first.root(), second.root());
    assert_ne!(first_claim.combined_row, second_claim.combined_row);
    assert!(verify_openings(
        first.root(),
        params,
        &first.open_columns(&[1usize, 6]).unwrap(),
        &first_claim,
        &gamma
    )
    .unwrap());
    assert!(verify_openings(
        second.root(),
        params,
        &second.open_columns(&[1usize, 6]).unwrap(),
        &second_claim,
        &gamma
    )
    .unwrap());
}

#[test]
fn systematic_openings_verify_bl2_input_claims_against_committed_witness() {
    let params = LigeroParams {
        row_len: 4,
        degree_bound: 4,
        codeword_len: 16,
        openings: 0,
        proximity_radius: 0,
        code: LigeroCode::Rs,
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

    assert!(verify_input_claims_from_systematic_openings_with_len(
        commitment.root(),
        params,
        &openings,
        &claims,
        8,
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
        code: LigeroCode::Rs,
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

    assert!(verify_input_claims_from_systematic_openings_with_len(
        commitment.root(),
        params,
        &commitment.open_systematic_columns().unwrap(),
        &claims,
        input_layer.len(),
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
        code: LigeroCode::Rs,
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
    assert!(!verify_input_claims_from_systematic_openings_with_len(
        commitment.root(),
        params,
        &openings,
        &claims,
        8,
    )
    .unwrap());

    let mut corrupt_openings = openings;
    corrupt_openings[0].column[0] = corrupt_openings[0].column[0] + Fp::ONE;
    assert!(!verify_input_claims_from_systematic_openings_with_len(
        commitment.root(),
        params,
        &corrupt_openings,
        &claims,
        8,
    )
    .unwrap());
}

#[test]
fn q007_v2_ligero_params_meet_zk_soundness_bounds() {
    let legacy = v1_ligero_params();
    assert!(legacy.validate().is_err());

    let option_a = v2_ligero_params();
    assert_eq!(option_a.row_len, 64);
    assert_eq!(option_a.degree_bound, 234);
    assert_eq!(option_a.codeword_len, 2048);
    assert_eq!(option_a.openings, 170);
    assert_eq!(option_a.proximity_radius, 875);
    option_a.validate().unwrap();
    assert!(option_a.degree_bound >= option_a.row_len + option_a.openings);
    assert!(option_a.soundness_error() <= 2f64.powi(-128));

    let option_b = v2_ligero_params_b();
    assert_eq!(option_b.row_len, 64);
    assert_eq!(option_b.degree_bound, 289);
    assert_eq!(option_b.codeword_len, 1024);
    assert_eq!(option_b.openings, 225);
    assert_eq!(option_b.proximity_radius, 335);
    option_b.validate().unwrap();
    assert!(option_b.degree_bound >= option_b.row_len + option_b.openings);
    assert!(option_b.soundness_error() <= 2f64.powi(-128));
}
