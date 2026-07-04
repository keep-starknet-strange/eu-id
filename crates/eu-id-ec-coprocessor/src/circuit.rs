use crate::{eq_eval, Fp};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct QuadTerm {
    pub out: u32,
    pub l: u32,
    pub r: u32,
    pub coeff: Fp,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Layer {
    out_log_size: usize,
    next_log_size: usize,
    terms: Vec<QuadTerm>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Circuit {
    layers: Vec<Layer>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CircuitError {
    EmptyCircuit,
    InvalidTermIndex,
    WrongPointLength {
        expected: usize,
        actual: usize,
    },
    WrongWitnessDepth {
        expected: usize,
        actual: usize,
    },
    WrongWitnessWidth {
        layer: usize,
        expected: usize,
        actual: usize,
    },
    RecurrenceMismatch {
        layer: usize,
        index: usize,
    },
}

impl Layer {
    pub fn new(
        out_log_size: usize,
        next_log_size: usize,
        terms: Vec<QuadTerm>,
    ) -> Result<Self, CircuitError> {
        let out_width = 1u32
            .checked_shl(out_log_size as u32)
            .ok_or(CircuitError::InvalidTermIndex)?;
        let next_width = 1u32
            .checked_shl(next_log_size as u32)
            .ok_or(CircuitError::InvalidTermIndex)?;
        if terms
            .iter()
            .any(|term| term.out >= out_width || term.l >= next_width || term.r >= next_width)
        {
            return Err(CircuitError::InvalidTermIndex);
        }
        Ok(Self {
            out_log_size,
            next_log_size,
            terms,
        })
    }

    pub fn out_log_size(&self) -> usize {
        self.out_log_size
    }

    pub fn next_log_size(&self) -> usize {
        self.next_log_size
    }

    pub fn terms(&self) -> &[QuadTerm] {
        &self.terms
    }

    pub fn q_tilde_eval(
        &self,
        r_out: &[Fp],
        left: &[Fp],
        right: &[Fp],
    ) -> Result<Fp, CircuitError> {
        if r_out.len() != self.out_log_size {
            return Err(CircuitError::WrongPointLength {
                expected: self.out_log_size,
                actual: r_out.len(),
            });
        }
        if left.len() != self.next_log_size {
            return Err(CircuitError::WrongPointLength {
                expected: self.next_log_size,
                actual: left.len(),
            });
        }
        if right.len() != self.next_log_size {
            return Err(CircuitError::WrongPointLength {
                expected: self.next_log_size,
                actual: right.len(),
            });
        }
        self.terms.iter().try_fold(Fp::ZERO, |acc, term| {
            let out = eq_eval(&bits(term.out, self.out_log_size), r_out).map_err(|_| {
                CircuitError::WrongPointLength {
                    expected: self.out_log_size,
                    actual: r_out.len(),
                }
            })?;
            let l = eq_eval(&bits(term.l, self.next_log_size), left).map_err(|_| {
                CircuitError::WrongPointLength {
                    expected: self.next_log_size,
                    actual: left.len(),
                }
            })?;
            let r = eq_eval(&bits(term.r, self.next_log_size), right).map_err(|_| {
                CircuitError::WrongPointLength {
                    expected: self.next_log_size,
                    actual: right.len(),
                }
            })?;
            Ok(acc + term.coeff * out * l * r)
        })
    }

    fn eval_next(&self, next: &[Fp]) -> Result<Vec<Fp>, CircuitError> {
        let expected = 1usize << self.next_log_size;
        if next.len() != expected {
            return Err(CircuitError::WrongWitnessWidth {
                layer: 0,
                expected,
                actual: next.len(),
            });
        }
        let mut out = vec![Fp::ZERO; 1usize << self.out_log_size];
        for term in &self.terms {
            out[term.out as usize] =
                out[term.out as usize] + term.coeff * next[term.l as usize] * next[term.r as usize];
        }
        Ok(out)
    }
}

impl Circuit {
    pub fn new(layers: Vec<Layer>) -> Result<Self, CircuitError> {
        if layers.is_empty() {
            return Err(CircuitError::EmptyCircuit);
        }
        for adjacent in layers.windows(2) {
            if adjacent[0].next_log_size != adjacent[1].out_log_size {
                return Err(CircuitError::InvalidTermIndex);
            }
        }
        Ok(Self { layers })
    }

    pub fn layers(&self) -> &[Layer] {
        &self.layers
    }

    pub fn evaluate_input(&self, input: Vec<Fp>) -> Result<Vec<Vec<Fp>>, CircuitError> {
        let input_log = self.layers.last().expect("non-empty").next_log_size;
        let expected = 1usize << input_log;
        if input.len() != expected {
            return Err(CircuitError::WrongWitnessWidth {
                layer: self.layers.len(),
                expected,
                actual: input.len(),
            });
        }

        let mut reversed = vec![input];
        for layer in self.layers.iter().rev() {
            let next = reversed.last().expect("has input");
            reversed.push(layer.eval_next(next)?);
        }
        reversed.reverse();
        Ok(reversed)
    }

    pub fn is_satisfied(&self, witness: &[Vec<Fp>]) -> Result<bool, CircuitError> {
        self.validate_witness(witness)?;
        Ok(witness[0].iter().all(|value| *value == Fp::ZERO))
    }

    fn validate_witness(&self, witness: &[Vec<Fp>]) -> Result<(), CircuitError> {
        let expected_depth = self.layers.len() + 1;
        if witness.len() != expected_depth {
            return Err(CircuitError::WrongWitnessDepth {
                expected: expected_depth,
                actual: witness.len(),
            });
        }
        for (layer_index, layer) in self.layers.iter().enumerate() {
            let expected_out = 1usize << layer.out_log_size;
            if witness[layer_index].len() != expected_out {
                return Err(CircuitError::WrongWitnessWidth {
                    layer: layer_index,
                    expected: expected_out,
                    actual: witness[layer_index].len(),
                });
            }
            let expected = layer.eval_next(&witness[layer_index + 1])?;
            for (index, (&actual, expected)) in
                witness[layer_index].iter().zip(expected).enumerate()
            {
                if actual != expected {
                    return Err(CircuitError::RecurrenceMismatch {
                        layer: layer_index,
                        index,
                    });
                }
            }
        }
        Ok(())
    }
}

fn bits(index: u32, width_log: usize) -> Vec<Fp> {
    (0..width_log)
        .map(|bit| Fp::from_u64(((index >> bit) & 1) as u64))
        .collect()
}
