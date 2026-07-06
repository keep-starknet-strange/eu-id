use blake2::{Blake2s256, Digest};

use crate::mac::{Gf128, GF128_BYTES};
use crate::Fp;

pub type TranscriptSeed = [u8; 32];

#[derive(Clone, Debug)]
pub struct CoprocessorChannel {
    state: Blake2s256,
    counter: u64,
}

impl CoprocessorChannel {
    pub fn from_seed(seed: TranscriptSeed, domain: &[u8]) -> Self {
        let mut state = Blake2s256::new();
        state.update((seed.len() as u64).to_be_bytes());
        state.update(seed);
        state.update((domain.len() as u64).to_be_bytes());
        state.update(domain);
        Self { state, counter: 0 }
    }

    pub fn mix_bytes(&mut self, bytes: &[u8]) {
        self.state.update((bytes.len() as u64).to_be_bytes());
        self.state.update(bytes);
    }

    pub fn mix_fp(&mut self, value: Fp) {
        self.mix_bytes(&value.to_bytes_be());
    }

    pub fn draw_fp(&mut self) -> Fp {
        let mut hasher = self.state.clone();
        hasher.update(self.counter.to_be_bytes());
        self.counter += 1;
        let digest = hasher.finalize();
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&digest);
        Fp::random(bytes)
    }

    pub fn draw_gf128(&mut self, label: &[u8]) -> Gf128 {
        self.mix_bytes(label);
        let mut hasher = self.state.clone();
        hasher.update(self.counter.to_be_bytes());
        self.counter += 1;
        let digest = hasher.finalize();
        let mut out = [0u8; GF128_BYTES];
        out.copy_from_slice(&digest[..GF128_BYTES]);
        out
    }
}
