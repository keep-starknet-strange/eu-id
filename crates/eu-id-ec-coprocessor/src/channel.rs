use blake2::{Blake2s256, Digest};

use crate::Fp;

#[derive(Clone, Debug)]
pub struct CoprocessorChannel {
    state: Blake2s256,
    counter: u64,
}

impl Default for CoprocessorChannel {
    fn default() -> Self {
        Self {
            state: Blake2s256::new(),
            counter: 0,
        }
    }
}

impl CoprocessorChannel {
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
}
