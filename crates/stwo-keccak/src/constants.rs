//! Keccak-f[1600] / SHAKE-256 structural constants.

/// Keccak-f state lanes (5x5).
pub const N_LANES_KECCAK: usize = 25;
/// Bytes per lane (u64 split into 8 little-endian 8-bit limbs).
pub const N_BYTES_IN_U64: usize = 8;
/// Total state bytes: 25 lanes x 8 bytes = 200.
pub const N_BYTES_IN_STATE: usize = N_LANES_KECCAK * N_BYTES_IN_U64;
/// Square root of the lane count (the 5 in 5x5).
pub const SQRT_N_LANES: usize = 5;
/// Rounds in Keccak-f[1600].
pub const N_ROUNDS: usize = 24;

/// SHAKE-256 rate in bytes (1088 bits). The capacity is 512 bits.
pub const N_BYTES_IN_RATE: usize = 136;
/// SHAKE-128 rate in bytes (1344 bits). The capacity is 256 bits.
pub const N_BYTES_IN_SHAKE128_RATE: usize = 168;
/// SHAKE domain-separation suffix byte (`0x1F` = `0b0001_1111`). The two low
/// bits `11` are the SHA-3 XOF domain tag. The next bit starts pad10*1.
pub const DELIMITED_SUFFIX: u8 = 0x1F;
/// Final padding bit OR-ed into the last rate byte (`0x80`).
pub const FINAL_BIT: u8 = 0x80;

/// Iota round constants from FIPS 202, plus zero for boundary row 24.
pub const IOTA_RC: [u64; N_ROUNDS + 1] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
    0x0000_0000_0000_0000, // fixed value for boundary row 24
];

/// Little-endian byte positions that vary in the Keccak Iota constants.
/// Bytes 2, 4, 5, and 6 are zero in every round and are inlined as zero.
pub const IOTA_RC_BYTE_INDICES: [usize; 4] = [0, 1, 3, 7];

/// Return the 24 Iota constants without the boundary-row-24 zero.
pub const fn iota_rc_rounds() -> [u64; N_ROUNDS] {
    let mut out = [0u64; N_ROUNDS];
    let mut i = 0;
    while i < N_ROUNDS {
        out[i] = IOTA_RC[i];
        i += 1;
    }
    out
}

/// Rho rotation offsets indexed `[x][y]`; lane index is `x + 5*y`.
/// `B[5*y + ((2x+3y) mod 5)] = rotl(A[x+5*y], RHO_OFFSETS[x][y])`.
pub const RHO_OFFSETS: [[usize; SQRT_N_LANES]; SQRT_N_LANES] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
