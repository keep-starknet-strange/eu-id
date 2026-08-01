# P5 proof-memory lifetime audit

Date: 2026-08-01

Status: implementation in progress.

The canonical path is `proveIdentity`. It creates one proof thread and one
local Rayon pool. It then builds the witness, commits trees zero through two,
runs the Keccak round GKR, and completes composition, FRI, queries, and
decommitment.

The committed trees must stay live until decommitment. Moving the GKR before
tree two would change the Fiat-Shamir order and is not allowed.

## Dominant project allocation

The Keccak carrier has 899 lookup slots at log size 13. `Fractions` stores each
gate numerator and relation denominator as `PackedQM31`:

- retained numerators: 112.375 MiB;
- retained denominators: 112.375 MiB;
- padded GKR input copies: 256 MiB.

The pinned STWO GKR prover also keeps the complete geometric layer chain. The
original fractions stay live because the post-GKR tie-back uses them.

Every carrier numerator is an M31 gate. Store these values as `PackedM31` and
use STWO `Layer::LogUpMultiplicities`. The canonical embedding into QM31 keeps
both required equations unchanged:

```text
claimed_sum = sum n(slot,row) / d(slot,row)
tie_back(row) = sum eq(slot,r_slot) * (delta*n(slot,row) + d(slot,row))
```

This representation change should reduce simultaneous peak memory by about
180.3 MiB. It must pass exact input-leaf, claimed-sum, GKR-proof-byte,
artifact, challenge, and tie-back parity tests before use.

The isolated candidate implements this change at commit
`21c65fb5e1d6c3bba96e632a0bd7c1430dc74b73`. An independent review found no
algebraic or protocol difference. The release test compared the complete GKR
proof bytes, artifact, transcript position, tie-back, coefficient MLE, and MLE
claim with the secure-field form. All 12 `stwo-keccak` library tests and Clippy
with warnings denied passed. The exact overlapping-allocation reduction is
189,038,592 bytes, or 180.28125 MiB. Peak RSS still needs a source-bound
measurement on the selected P4 point.

## Other bounded changes

`global_claimed_sum` allocates a 112.375 MiB inverse vector. Process the same
denominators in bounded ordered chunks. Preserve the exact pointwise inverses
and accumulation order. This can remove most of the temporary allocation, but
it may not reduce HWM if the later GKR layer chain remains the peak.

Candidate commit `f3d79527` uses fixed chunks of 2,048 packed denominators. It
keeps the flattened slot and row order and the final SIMD-lane reduction order.
The generic proof-byte parity fixture spans more than one chunk. The 12 release
library tests, formatting, and Clippy with warnings denied passed.

Moving the base-field numerator buffer into the GKR layer can save another
28.1 MiB. Do this only after the representation change is measured. The
tie-back must then reconstruct the canonical numerator schedule exactly.

Do not implement commitment overlap. It would increase the number of live
trees. Do not change the pinned STWO prover unless project-side changes are
insufficient and proof-byte parity is established.

## ARM acceleration

The Android target enables the `neon` target feature. The pinned STWO revision
selects its AArch64 NEON multiplication functions for the FFT path, and the
canonical proof uses `SimdBackend`.

The current AAR contains a stripped AArch64 `libeuid_zk_sdk.so`. A disassembly
of that exact library contains 5,589 NEON multiply instructions. One observed
instruction is `umull v4.2d, v1.2s, v2.2s`. This proves that the current mobile
artifact uses NEON. No scalar-fallback change is needed.

## Stack and P6 audit

The SDK fixes both the outer proof-thread stack and each local Rayon worker
stack at 64 MiB. `RUST_MIN_STACK` does not change these values. The proof work
runs on a Rayon worker, so the worker stack is the safety-critical value. An
old 2 MiB worker stack overflowed. A 32 MiB stack passed an older 202-permutation
test, but this does not prove that it is safe for the current all-ML-DSA-65
circuit.

After P4 selection, use temporary private Android arguments to sweep worker
stacks of 64, 48, 32, 24, and 16 MiB. Keep the outer stack at 64 MiB. Then
sweep outer stacks of 64, 8, and 2 MiB with the smallest stable worker stack.
Use the same APK, fresh processes, and counterordered runs on all three phones.
Remove the temporary controls and hard-code the selected values.

Current phase evidence does not activate P6. Witness generation is 4.8% to
5.9% of the available phone runs and about 6% on desktop. The AIR core is the
binding phase. Recheck the final selected-circuit phase record before closing
P6.
