use crate::Fp;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mle {
    values: Vec<Fp>,
    num_vars: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MleError {
    WrongPointLength { expected: usize, actual: usize },
}

impl Mle {
    pub fn new(mut values: Vec<Fp>) -> Self {
        let len = values.len().max(1).next_power_of_two();
        values.resize(len, Fp::ZERO);
        Self {
            num_vars: len.ilog2() as usize,
            values,
        }
    }

    pub fn values(&self) -> &[Fp] {
        &self.values
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub fn eval_at(&self, point: &[Fp]) -> Result<Fp, MleError> {
        if point.len() != self.num_vars {
            return Err(MleError::WrongPointLength {
                expected: self.num_vars,
                actual: point.len(),
            });
        }
        let mut values = self.values.clone();
        for &challenge in point {
            values = fix_first_values(&values, challenge);
        }
        Ok(values[0])
    }

    pub fn fix_first_variable(&self, challenge: Fp) -> Result<Self, MleError> {
        if self.num_vars == 0 {
            return Err(MleError::WrongPointLength {
                expected: 1,
                actual: 0,
            });
        }
        let values = fix_first_values(&self.values, challenge);
        Ok(Self {
            num_vars: self.num_vars - 1,
            values,
        })
    }
}

pub fn eq_eval(lhs: &[Fp], rhs: &[Fp]) -> Result<Fp, MleError> {
    if lhs.len() != rhs.len() {
        return Err(MleError::WrongPointLength {
            expected: lhs.len(),
            actual: rhs.len(),
        });
    }
    Ok(lhs.iter().zip(rhs.iter()).fold(Fp::ONE, |acc, (&a, &b)| {
        acc * (a * b + (Fp::ONE - a) * (Fp::ONE - b))
    }))
}

fn fix_first_values(values: &[Fp], challenge: Fp) -> Vec<Fp> {
    values
        .chunks_exact(2)
        .map(|pair| pair[0] + challenge * (pair[1] - pair[0]))
        .collect()
}
