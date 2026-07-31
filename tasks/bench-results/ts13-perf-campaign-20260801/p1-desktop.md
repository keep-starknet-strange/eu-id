# P1 canonical-path overhead

Date: 2026-08-01

P1 removes a second scalar replay of all Keccak rounds. The round component now
uses the ordered boundary rows that the canonical Keccak trace already builds.
The trace generator builds independent permutations in parallel and preserves
their input order.

## Provenance

- Source commit: `6a360bf166a81d371b3d8ee6fee204beb44edb3b`
- Circuit hash: `64da83bf7846f3ec90a881e121c7d598f9b2f743113f2911cde347b303ea4b1e`
- Shape manifest SHA-256: `fbe394a6f265b06589db03f1e31a353203b0707e290eaba8aecf78ab1a77b748`
- Soundness source-tree SHA-256: `5496d563a85bd45d0ad1b204de2cf7cbc1634403332a2cb5fb52e9c34a4b9e8e`
- Frozen benchmark binary SHA-256: `1b4a40bd23d5b78c07092c1c8f60c52b358834a3facdbdc658b185a40f226935`
- Proof envelope: 1,638,446 bytes
- Host: Apple M2 Max, 12 CPU cores, 32 GB RAM
- Build: native AArch64 release, fat LTO, one code-generation unit
- Runtime: 12 Rayon workers and a 512 MiB minimum stack limit

The circuit geometry is unchanged. The source-bound circuit and source-tree
hashes changed because the prover source changed.

## Cold timing-enabled samples

Each row is a fresh process and one canonical `proveIdentity` call.

| Sample | Prove | Verify | Witness | AIR core | SDK total |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1,783 ms | 54 ms | 71.324 ms | 1,707.921 ms | 1,782.548 ms |
| 2 | 1,431 ms | 42 ms | 72.706 ms | 1,356.242 ms | 1,431.331 ms |
| 3 | 1,385 ms | 44 ms | 72.398 ms | 1,310.055 ms | 1,384.735 ms |
| 4 | 1,316 ms | 40 ms | 74.275 ms | 1,239.560 ms | 1,315.878 ms |
| 5 | 1,324 ms | 43 ms | 74.613 ms | 1,247.768 ms | 1,324.374 ms |
| 6 | 1,362 ms | 44 ms | 73.653 ms | 1,286.446 ms | 1,362.128 ms |
| 7 | 1,296 ms | 41 ms | 73.823 ms | 1,219.882 ms | 1,295.673 ms |
| **Median** | **1,362 ms** | **43 ms** | **73.653 ms** | **1,286.446 ms** | **1,362.128 ms** |

The median canonical-to-AIR ratio is `1.059`. This passes the P1 limit of
`1.15`. The previous ratio was `1.162`. Median witness generation fell from
191.302 ms to 73.653 ms, a 61.5% reduction.

## Cold timing-disabled samples

| Sample | Prove | Verify | Peak RSS |
| ---: | ---: | ---: | ---: |
| 1 | 1,674 ms | 44 ms | 1,886,928,896 B |
| 2 | 1,255 ms | 38 ms | 2,182,348,800 B |
| 3 | 1,328 ms | 41 ms | 2,178,629,632 B |
| 4 | 1,275 ms | 41 ms | 2,172,420,096 B |
| 5 | 1,438 ms | 40 ms | 2,172,043,264 B |
| 6 | 1,348 ms | 40 ms | 2,174,418,944 B |
| 7 | 1,329 ms | 39 ms | 2,177,531,904 B |
| **Median** | **1,329 ms** | **40 ms** | **2,174,418,944 B** |

The previous untimed median was 1,368 ms. P1 improves it by 39 ms, or 2.9%.
The median peak RSS is 2,073.69 MiB, which is within measurement noise of the
previous 2,071.12 MiB.

## Pixel 8 result

The phone measurement used the same P1 checkpoint in a detached clean
worktree. It ran one cold release instrumentation test on Firebase model
`shiba`, Android API 34.

- Android AAR SHA-256: `8ed1b2a9d1b99702bd018b89553ee79f710dd216949e4e8e8c56f89d4bb387b6`
- Host APK SHA-256: `56c78e9498d1e597075cfee638bf37cb0da47cb12b0c2bfc2edf1eff8f313f27`
- Test APK SHA-256: `2d31c3593796fb21c9f38dc658017ded178a6902d8a5a74cd8a538dd48a24e35`
- Fixture SHA-256: `0ba93c225b49de29842300584787f7c4f1d3c75745d791152cf603a68b156bf4`
- Firebase matrix: `matrix-26ifimb8gvh6b`
- [Firebase result](https://console.firebase.google.com/project/exploration-dev-417917/testlab/histories/bh.a21b73b77a063202/matrices/8716527956927216949)

| Metric | P0 | P1 | Change |
| --- | ---: | ---: | ---: |
| Prove | 9,578 ms | 7,986 ms | −1,592 ms (−16.6%) |
| Verify | 254 ms | 224 ms | −30 ms |
| Witness generation | 1,190.715 ms | 505.737 ms | −684.978 ms (−57.5%) |
| AIR core | 8,324.672 ms | 7,417.405 ms | −907.267 ms |
| Peak RSS | 1,989,380 KiB | 1,989,876 KiB | +496 KiB |
| Envelope | 1,638,446 B | 1,638,446 B | unchanged |

The P1 Pixel canonical-to-AIR ratio is `1.072`. One cold sample is the
campaign's phone convention; the final operating point must be measured again
on all three devices.
