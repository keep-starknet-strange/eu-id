//! Native SHAKE shape metadata shared by the Keccak service.
//!
//! The proof AIR lives in [`crate::sponge_v`] and [`crate::service`]. This file
//! intentionally keeps only the public shape/XOF surface and the native
//! Keccak-f byte permutation used to build service witnesses.

use serde::{
    de::Error as DeError, ser::Error as SerError, Deserialize, Deserializer, Serialize, Serializer,
};

use crate::constants::{N_BYTES_IN_RATE, N_BYTES_IN_STATE, N_BYTES_IN_U64};

/// Number of permutations a `(n_absorb, n_squeeze)` sponge performs.
pub const fn n_perms(n_absorb: usize, n_squeeze: usize) -> usize {
    n_absorb + n_squeeze - 1
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
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    pub xof_mode: XofMode,
    /// Public byte length that is absorbed by this job.
    pub message_len: usize,
    /// Fixed allocation bound for a capacity-shaped job. With `None`,
    /// `message_len` also defines the fixed shape.
    ///
    /// Capacity-shaped jobs still bind `message_len` into the public
    /// transcript, but derive their row count and preprocessed schedule from
    /// this value. They are intentionally limited to one squeeze block: this
    /// is the request-sized ML-DSA µ job, whose final absorb permutation is
    /// also its only squeeze row.
    /// This profile parameter is deliberately not proof-serialized. A service
    /// verifier must reconstruct the bounded shape from its semantic public
    /// message and circuit artifact; serializing a capacity-shaped `Shape`
    /// fails instead of treating it as a fixed-length shape.
    pub message_capacity: Option<usize>,
    pub n_absorb: usize,
    pub n_squeeze: usize,
    pub absorb_stream_id: u32,
    pub squeeze_stream_id: u32,
    pub perm_id_base: usize,
}

/// Fixed-shape wire format.
///
/// The field order defines the serialized format. Capacity shapes are not
/// serialized. The verifier reconstructs them from its profile.
#[derive(Serialize, Deserialize)]
struct FixedShapeWire {
    xof_mode: XofMode,
    message_len: usize,
    n_absorb: usize,
    n_squeeze: usize,
    absorb_stream_id: u32,
    squeeze_stream_id: u32,
    perm_id_base: usize,
}

impl Serialize for Shape {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if self.message_capacity.is_some() {
            return Err(S::Error::custom(
                "capacity-shaped sponge jobs must be reconstructed from the verifier profile",
            ));
        }
        FixedShapeWire {
            xof_mode: self.xof_mode,
            message_len: self.message_len,
            n_absorb: self.n_absorb,
            n_squeeze: self.n_squeeze,
            absorb_stream_id: self.absorb_stream_id,
            squeeze_stream_id: self.squeeze_stream_id,
            perm_id_base: self.perm_id_base,
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Shape {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = FixedShapeWire::deserialize(deserializer)?;
        if wire.n_squeeze == 0 {
            return Err(D::Error::custom(
                "sponge shape must contain at least one squeeze block",
            ));
        }
        if wire.xof_mode == XofMode::Shake128 && wire.message_len > N_BYTES_IN_RATE {
            return Err(D::Error::custom(format_args!(
                "SHAKE-128 service messages must not exceed {N_BYTES_IN_RATE} bytes"
            )));
        }
        let expected_n_absorb = (wire.message_len + 1).div_ceil(wire.xof_mode.rate());
        if wire.n_absorb != expected_n_absorb {
            return Err(D::Error::custom(format_args!(
                "invalid fixed sponge geometry: encoded {} absorb rows, expected {expected_n_absorb}",
                wire.n_absorb
            )));
        }
        Ok(Self {
            xof_mode: wire.xof_mode,
            message_len: wire.message_len,
            message_capacity: None,
            n_absorb: wire.n_absorb,
            n_squeeze: wire.n_squeeze,
            absorb_stream_id: wire.absorb_stream_id,
            squeeze_stream_id: wire.squeeze_stream_id,
            perm_id_base: wire.perm_id_base,
        })
    }
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
            None,
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            0,
        )
    }

    /// A SHAKE-128 service shape. The message can contain at most 136 bytes.
    /// The squeeze rate stays at 168 bytes.
    pub fn shake128(
        message_len: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
    ) -> Self {
        Self::with_mode_and_perm_id_base(
            XofMode::Shake128,
            message_len,
            None,
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
            None,
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            perm_id_base,
        )
    }

    /// A SHAKE-256 job whose proof geometry is fixed by `message_capacity`
    /// while its SHAKE padding and transcript use the public `message_len`.
    ///
    /// The one-squeeze restriction keeps the allocated maximum absorb rows
    /// contiguous: the actual final absorb row is also the output row, and
    /// every later allocated row is a canonical independent zero-state
    /// permutation.
    pub fn with_message_capacity(
        message_len: usize,
        message_capacity: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
    ) -> Result<Self, ShapeError> {
        if message_len > message_capacity {
            return Err(ShapeError::MessageExceedsCapacity {
                message_len,
                message_capacity,
            });
        }
        if n_squeeze != 1 {
            return Err(ShapeError::CapacityModeRequiresOneSqueeze { n_squeeze });
        }
        Ok(Self::with_mode_and_perm_id_base(
            XofMode::Shake256,
            message_len,
            Some(message_capacity),
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            0,
        ))
    }

    fn with_mode_and_perm_id_base(
        xof_mode: XofMode,
        message_len: usize,
        message_capacity: Option<usize>,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
        perm_id_base: usize,
    ) -> Self {
        assert!(n_squeeze >= 1, "at least one squeeze block");
        assert!(
            xof_mode != XofMode::Shake128 || message_len <= N_BYTES_IN_RATE,
            "SHAKE-128 service messages must not exceed {N_BYTES_IN_RATE} bytes"
        );
        let geometry_message_len = message_capacity.unwrap_or(message_len);
        Self {
            xof_mode,
            message_len,
            message_capacity,
            n_absorb: (geometry_message_len + 1).div_ceil(xof_mode.rate()),
            n_squeeze,
            absorb_stream_id,
            squeeze_stream_id,
            perm_id_base,
        }
    }

    pub(crate) fn with_rebased_perm_ids(self, perm_id_base: usize) -> Self {
        Self {
            perm_id_base,
            ..self
        }
    }

    /// Length from which the allocation and schedule are derived.
    pub const fn geometry_message_len(&self) -> usize {
        match self.message_capacity {
            Some(capacity) => capacity,
            None => self.message_len,
        }
    }

    pub const fn has_message_capacity(&self) -> bool {
        self.message_capacity.is_some()
    }

    /// Actual absorb rows, including the row containing SHAKE padding.
    pub const fn actual_n_absorb(&self) -> usize {
        (self.message_len + 1).div_ceil(self.rate())
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShapeError {
    MessageExceedsCapacity {
        message_len: usize,
        message_capacity: usize,
    },
    CapacityModeRequiresOneSqueeze {
        n_squeeze: usize,
    },
}

impl core::fmt::Display for ShapeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::MessageExceedsCapacity {
                message_len,
                message_capacity,
            } => write!(
                f,
                "message length {message_len} exceeds fixed capacity {message_capacity}"
            ),
            Self::CapacityModeRequiresOneSqueeze { n_squeeze } => write!(
                f,
                "fixed-capacity sponge jobs require one squeeze block, got {n_squeeze}"
            ),
        }
    }
}

impl std::error::Error for ShapeError {}

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
    state[0] ^= crate::constants::IOTA_RC[round];
}
