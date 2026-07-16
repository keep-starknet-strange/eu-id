use eu_id_ec_coprocessor::{eq_eval, Fp, Mle};

#[test]
fn mle_new_pads_to_next_power_of_two() {
    let mle = Mle::new(vec![Fp::from_u64(1), Fp::from_u64(2), Fp::from_u64(3)]);

    assert_eq!(
        mle.values(),
        &[Fp::from_u64(1), Fp::from_u64(2), Fp::from_u64(3), Fp::ZERO]
    );
    assert_eq!(mle.num_vars(), 2);
}

#[test]
fn mle_eval_matches_boolean_corners_and_midpoint_average() {
    let mle = Mle::new(vec![
        Fp::from_u64(2),
        Fp::from_u64(4),
        Fp::from_u64(6),
        Fp::from_u64(8),
    ]);

    assert_eq!(mle.eval_at(&[Fp::ZERO, Fp::ZERO]).unwrap(), Fp::from_u64(2));
    assert_eq!(mle.eval_at(&[Fp::ONE, Fp::ZERO]).unwrap(), Fp::from_u64(4));
    assert_eq!(mle.eval_at(&[Fp::ZERO, Fp::ONE]).unwrap(), Fp::from_u64(6));
    assert_eq!(mle.eval_at(&[Fp::ONE, Fp::ONE]).unwrap(), Fp::from_u64(8));

    let half = Fp::from_u64(2).inverse().unwrap();
    let expected =
        (Fp::from_u64(2) + Fp::from_u64(4) + Fp::from_u64(6) + Fp::from_u64(8)) * half * half;
    assert_eq!(mle.eval_at(&[half, half]).unwrap(), expected);
}

#[test]
fn fix_first_variable_matches_direct_evaluation() {
    let mle = Mle::new((0u64..8).map(Fp::from_u64).collect());
    let fixed = mle.fix_first_variable(Fp::from_u64(9)).unwrap();
    let tail = [Fp::from_u64(3), Fp::from_u64(4)];

    assert_eq!(
        fixed.eval_at(&tail).unwrap(),
        mle.eval_at(&[Fp::from_u64(9), tail[0], tail[1]]).unwrap()
    );
}

#[test]
fn equality_polynomial_is_one_only_at_matching_boolean_point() {
    let point = [Fp::ONE, Fp::ZERO, Fp::ONE];

    assert_eq!(
        eq_eval(&point, &[Fp::ONE, Fp::ZERO, Fp::ONE]).unwrap(),
        Fp::ONE
    );
    assert_eq!(
        eq_eval(&point, &[Fp::ZERO, Fp::ZERO, Fp::ONE]).unwrap(),
        Fp::ZERO
    );
    assert!(eq_eval(&point, &[Fp::ONE]).is_err());
}
