use eu_id_ec_coprocessor::{eq_eval, Circuit, Fp, Layer, QuadTerm};

fn term(out: u32, l: u32, r: u32, coeff: u64) -> QuadTerm {
    QuadTerm {
        out,
        l,
        r,
        coeff: Fp::from_u64(coeff),
    }
}

fn bits(index: u32, width_log: usize) -> Vec<Fp> {
    (0..width_log)
        .map(|bit| Fp::from_u64(((index >> bit) & 1) as u64))
        .collect()
}

fn brute_q(layer: &Layer, r_out: &[Fp], left: &[Fp], right: &[Fp]) -> Fp {
    layer.terms().iter().fold(Fp::ZERO, |acc, t| {
        acc + t.coeff
            * eq_eval(&bits(t.out, layer.out_log_size()), r_out).unwrap()
            * eq_eval(&bits(t.l, layer.next_log_size()), left).unwrap()
            * eq_eval(&bits(t.r, layer.next_log_size()), right).unwrap()
    })
}

#[test]
fn sparse_q_tilde_matches_bruteforce_sum() {
    let layer = Layer::new(2, 2, vec![term(0, 1, 2, 3), term(3, 2, 1, 9)]).unwrap();
    let r_out = [Fp::from_u64(5), Fp::from_u64(7)];
    let left = [Fp::from_u64(11), Fp::from_u64(13)];
    let right = [Fp::from_u64(17), Fp::from_u64(19)];

    assert_eq!(
        layer.q_tilde_eval(&r_out, &left, &right).unwrap(),
        brute_q(&layer, &r_out, &left, &right)
    );
}

#[test]
fn layered_circuit_evaluates_quad_terms() {
    let layer = Layer::new(1, 1, vec![term(0, 0, 1, 1), term(1, 1, 1, 1)]).unwrap();
    let circuit = Circuit::new(vec![layer]).unwrap();
    let input = vec![Fp::from_u64(3), Fp::from_u64(5)];

    let witness = circuit.evaluate_input(input).unwrap();

    assert_eq!(witness[1], vec![Fp::from_u64(3), Fp::from_u64(5)]);
    assert_eq!(witness[0], vec![Fp::from_u64(15), Fp::from_u64(25)]);
    assert!(!circuit.is_satisfied(&witness).unwrap());
}

#[test]
fn satisfied_requires_zero_output_layer() {
    let layer = Layer::new(1, 1, vec![term(0, 0, 0, 1)]).unwrap();
    let circuit = Circuit::new(vec![layer]).unwrap();
    let witness = circuit
        .evaluate_input(vec![Fp::ZERO, Fp::from_u64(5)])
        .unwrap();

    assert_eq!(witness[0][0], Fp::ZERO);
    assert!(circuit.is_satisfied(&witness).unwrap());
}
