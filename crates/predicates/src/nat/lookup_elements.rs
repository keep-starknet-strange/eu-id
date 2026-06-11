use crate::nat::table::NatTableElements;
use stwo::core::channel::Channel;

#[derive(Clone)]
pub struct LookupElements {
    pub nat_table: NatTableElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            nat_table: NatTableElements::draw(channel),
        }
    }
}
