use crate::nat::table::{NatTableElements, SignedNatTableElements};
use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

relation!(NatPrefixTransitionElements, 2);

#[derive(Clone)]
pub struct LookupElements {
    pub nat_table: NatTableElements,
    pub signed_valid: SignedNatTableElements,
    pub prefix_transition: NatPrefixTransitionElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            nat_table: NatTableElements::draw(channel),
            signed_valid: SignedNatTableElements::draw(channel),
            prefix_transition: NatPrefixTransitionElements::draw(channel),
        }
    }
}
