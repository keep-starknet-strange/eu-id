use air_core::Air;
use num_traits::Zero;
use stwo::core::fields::qm31::SecureField;
use stwo_sha256::air::Sha256Verifier;
use stwo_sha256::interaction::{ComponentClaim, InteractionClaim};

#[test]
fn verifier_accepts_only_the_local_or_shared_range_claim_shape() {
    let zero = SecureField::zero();
    let local = InteractionClaim {
        sha256: ComponentClaim { claimed_sum: zero },
        range: (0..4)
            .map(|_| ComponentClaim { claimed_sum: zero })
            .collect(),
    };
    assert!(Sha256Verifier::new(9, local).validate_structure().is_ok());

    let shared = InteractionClaim {
        sha256: ComponentClaim { claimed_sum: zero },
        range: vec![],
    };
    assert!(Sha256Verifier::new(9, shared).validate_structure().is_err());
}
