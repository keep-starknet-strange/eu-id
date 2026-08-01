# P2 all-ML-DSA-65 Keccak carrier

Date: 2026-08-01

Status: complete. P4 and P5 still use this circuit as their input.

The privacy claim is `public-input unlinkable; transcript zero knowledge pending`.
The issuer, device, and revocation roles all use ML-DSA-65.

## Provenance

- Soundness source commit: `4e14f09df39f2820f3c2eaffe433a16ad62b9b2a`
- Artifact commit: `95e5f9a820904e32abb39a3eedfcf04f52cf88be`
- Circuit hash: `4d55b4e5cb6d4fab102395d3647d267d3f3116e6cabae9e33f3c957f7e07c2b2`
- Shape manifest SHA-256: `a5c8c6fdbaac8e1a9b0ca81704b31c7e29f2ec27487f603139531c39faf42d60`
- Soundness source-tree SHA-256: `bc6171874fd1383c6dfc457af3301b5c36b24d8e5201f96f35162c124e9111c3`
- Generation-input SHA-256: `60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0`
- Cargo.lock SHA-256: `23e70c964b943632fed547cfa38e6c1d24cfeac070a3518bc0f1a704f7597dbe`
- Rust toolchain file SHA-256: `8f0604004d13f7a26332366e59ba731bbb6046aaf789439d760abf67ad78589f`
- Benchmark binary SHA-256: `f146d04a54a6809e65daf04e68bc5945c81e2a62c6790a43619c4fd05a264bb9`
- PCS checkpoint: blowup 3, 36 queries, 20 proof-of-work bits, lifting log size 19
- Fixed proof body capacity: 1,572,864 bytes
- Fixed identity-proof envelope: 1,572,910 bytes

## Geometry

- Keccak permutations: 261
- Carrier rows: 8,192 at log size 13
- Carrier columns: 910
- Live carrier lookups per row: 899
- Preprocessed cells: 211,104
- Trace cells: 8,121,376
- Interaction cells: 704,640
- Post-interaction cells: 65,536
- Total committed Keccak cells: 9,102,656
- Shared relation draws: 87
- Active relation uses: 251
- Reserved transcript relation: `r07_keccak_round`

The total is below the 9,200,000-cell P2 gate. It is 29.2% below the old
12,850,176-cell service. The cleanup also removes a dead 12.94 MiB round-link
witness payload. That payload did not enter a committed column.

## Cold desktop result

The host is an Apple M2 Max with 12 CPU cores and 32 GB of memory. Each row is
one fresh process. The release build used 12 Rayon workers.

| Sample | Prove | Verify |
| ---: | ---: | ---: |
| 1 | 1,330 ms | 38 ms |
| 2 | 1,555 ms | 39 ms |
| 3 | 1,337 ms | 40 ms |
| 4 | 1,359 ms | 37 ms |
| 5 | 1,324 ms | 37 ms |
| 6 | 1,489 ms | 43 ms |
| 7 | 1,464 ms | 41 ms |
| **Median** | **1,359 ms** | **39 ms** |

One additional cold sample took 1,469 ms. Its maximum resident set was
1,889,501,184 bytes. Its peak memory footprint was 1,688,422,656 bytes.

## Verification

- The release workspace check passed for all targets.
- The 46-test Keccak release suite passed.
- The exact n=261 geometry and denominator-oracle tests passed.
- The all-ML-DSA-65 role, wire-profile, SHA, device-key, and MSO census tests passed.
- All seven credential fixture tests passed.
- The verified composed proof refreshed the live artifact input.
- The composed proof then passed against the regenerated artifact.
- All 14 artifact schema, source-binding, and drift tests passed.

The final proof-level negative matrices and mobile results belong to the final
P4 and P5 checkpoint. They are not claimed by this P2 record.
