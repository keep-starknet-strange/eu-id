use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarArithmeticError {
    InvalidBound {
        bound_name: &'static str,
    },
    NonCanonical {
        value_name: &'static str,
        bound_name: &'static str,
    },
    ZeroValue {
        value_name: &'static str,
    },
    InvalidBoolean {
        name: &'static str,
        value: u32,
    },
    LimbOutOfRange {
        value_name: &'static str,
        limb: usize,
        value: u32,
    },
    LimbEquationRemainder {
        equation: &'static str,
        limb: usize,
        total: i64,
    },
    CarryMismatch {
        equation: &'static str,
        limb: usize,
        expected: i64,
        actual: i64,
    },
    FinalCarryNonZero {
        equation: &'static str,
        carry: i64,
    },
    TraceMismatch {
        value_name: &'static str,
    },
    UnexpectedProductRemainder {
        equation: &'static str,
    },
}

impl fmt::Display for ScalarArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBound { bound_name } => {
                write!(f, "{bound_name} must be a nonzero canonical bound")
            }
            Self::NonCanonical {
                value_name,
                bound_name,
            } => write!(f, "{value_name} is not strictly less than {bound_name}"),
            Self::ZeroValue { value_name } => write!(f, "{value_name} must be nonzero"),
            Self::InvalidBoolean { name, value } => {
                write!(f, "{name} must be boolean, got {value}")
            }
            Self::LimbOutOfRange {
                value_name,
                limb,
                value,
            } => write!(f, "{value_name}[{limb}] = {value} is outside 13-bit range"),
            Self::LimbEquationRemainder {
                equation,
                limb,
                total,
            } => write!(
                f,
                "{equation} limb {limb} total {total} is not divisible by limb radix"
            ),
            Self::CarryMismatch {
                equation,
                limb,
                expected,
                actual,
            } => write!(
                f,
                "{equation} limb {limb} carry mismatch: expected {expected}, got {actual}"
            ),
            Self::FinalCarryNonZero { equation, carry } => {
                write!(f, "{equation} final carry must be zero, got {carry}")
            }
            Self::TraceMismatch { value_name } => {
                write!(f, "{value_name} trace does not match its parent trace")
            }
            Self::UnexpectedProductRemainder { equation } => {
                write!(
                    f,
                    "{equation} product remainder does not match expected result"
                )
            }
        }
    }
}

impl std::error::Error for ScalarArithmeticError {}
