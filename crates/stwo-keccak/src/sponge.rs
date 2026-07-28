//! Native SHAKE shape metadata shared by the Keccak service.
//!
//! The proof AIR lives in [`crate::sponge_v`] and [`crate::service`]. This file
//! intentionally keeps only the public shape/XOF surface and the native
//! Keccak-f byte permutation used to build service witnesses.

use serde::{Deserialize, Serialize};

use crate::constants::{N_BYTES_IN_RATE, N_BYTES_IN_STATE, N_BYTES_IN_U64};

/// Number of permutations a `(n_absorb, n_squeeze)` sponge performs.
pub const fn n_perms(n_absorb: usize, n_squeeze: usize) -> usize {
    n_absorb + n_squeeze - 1
}

/// Number of absorb blocks needed for a message of `l` bytes (pad10*1 always
/// adds at least one padding byte, so `ceil((l+1)/rate)` for SHAKE-256).
pub const fn n_absorb_blocks(l: usize) -> usize {
    (l + 1).div_ceil(N_BYTES_IN_RATE)
}

/// SHAKE variant and therefore sponge rate.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum XofMode {
    Shake256,
    Shake128,
}

impl XofMode {
    pub const fn rate(self) -> usize {
        match self {
            Self::Shake256 => N_BYTES_IN_RATE,
            Self::Shake128 => crate::constants::N_BYTES_IN_SHAKE128_RATE,
        }
    }

    pub const fn transcript_tag(self) -> u64 {
        match self {
            Self::Shake256 => 256,
            Self::Shake128 => 128,
        }
    }
}

/// Static shape of a sponge job.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Shape {
    pub xof_mode: XofMode,
    pub message_len: usize,
    pub n_absorb: usize,
    pub n_squeeze: usize,
    pub absorb_stream_id: u32,
    pub squeeze_stream_id: u32,
    pub perm_id_base: usize,
}

impl Shape {
    pub fn new(
        message_len: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
    ) -> Self {
        Self::with_mode_and_perm_id_base(
            XofMode::Shake256,
            message_len,
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            0,
        )
    }

    /// A SHAKE-128 service shape.
    pub fn shake128(
        message_len: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
    ) -> Self {
        Self::with_mode_and_perm_id_base(
            XofMode::Shake128,
            message_len,
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            0,
        )
    }

    /// [`Shape::new`] with an explicit global `perm_id_base`.
    pub fn with_perm_id_base(
        message_len: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
        perm_id_base: usize,
    ) -> Self {
        Self::with_mode_and_perm_id_base(
            XofMode::Shake256,
            message_len,
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            perm_id_base,
        )
    }

    fn with_mode_and_perm_id_base(
        xof_mode: XofMode,
        message_len: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
        perm_id_base: usize,
    ) -> Self {
        assert!(n_squeeze >= 1, "at least one squeeze block");
        Self {
            xof_mode,
            message_len,
            n_absorb: (message_len + 1).div_ceil(xof_mode.rate()),
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            perm_id_base,
        }
    }

    pub(crate) fn with_rebased_perm_ids(self, perm_id_base: usize) -> Self {
        Self::with_mode_and_perm_id_base(
            self.xof_mode,
            self.message_len,
            self.n_squeeze,
            self.absorb_stream_id,
            self.squeeze_stream_id,
            perm_id_base,
        )
    }

    pub const fn rate(&self) -> usize {
        self.xof_mode.rate()
    }

    pub fn n_perms(&self) -> usize {
        n_perms(self.n_absorb, self.n_squeeze)
    }

    pub fn output_len(&self) -> usize {
        self.n_squeeze * self.rate()
    }
}

/// Native Keccak-f on a byte-state, via the u64 path.
pub(crate) fn native_keccak_f_bytes(state: &mut [u8; N_BYTES_IN_STATE]) {
    let mut words = [0u64; 25];
    for (w, word) in words.iter_mut().enumerate() {
        for b in 0..N_BYTES_IN_U64 {
            *word |= (state[w * N_BYTES_IN_U64 + b] as u64) << (8 * b);
        }
    }
    keccak_f_words(&mut words);
    for (w, &word) in words.iter().enumerate() {
        for b in 0..N_BYTES_IN_U64 {
            state[w * N_BYTES_IN_U64 + b] = ((word >> (8 * b)) & 0xFF) as u8;
        }
    }
}

fn keccak_f_words(state: &mut [u64; 25]) {
    for round in 0..crate::constants::N_ROUNDS {
        keccak_round_words(state, round);
    }
}

fn keccak_round_words(state: &mut [u64; 25], round: usize) {
    const RHO: [u32; 24] = [
        1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
    ];
    const PI: [usize; 24] = [
        10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
    ];
    let rc = crate::constants::iota_rc_rounds();
    let mut c = [0u64; 5];
    for x in 0..5 {
        c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    }
    let mut d = [0u64; 5];
    for x in 0..5 {
        d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
    }
    for y in 0..5 {
        for x in 0..5 {
            state[x + 5 * y] ^= d[x];
        }
    }
    let mut current = state[1];
    for i in 0..24 {
        let idx = PI[i];
        let tmp = state[idx];
        state[idx] = current.rotate_left(RHO[i]);
        current = tmp;
    }
    for y in 0..5 {
        let base = 5 * y;
        let row: [u64; 5] = std::array::from_fn(|x| state[base + x]);
        for x in 0..5 {
            state[base + x] = row[x] ^ ((!row[(x + 1) % 5]) & row[(x + 2) % 5]);
        }
    }
    state[0] ^= rc[round];
}
