# P3 compact SHA-256 trace

Date: 2026-08-01

P3 commits only the rolling `a` and `e` SHA-256 state lanes. It derives the
other state lanes from row offsets. The canonical item and MSO paths now use
1,320,640 committed cells. This result is 179,360 cells below the P3 limit.

## Provenance

- Source commit: `b878b43aa43ec184b9c393042d92d3d2a9fee04d`
- Artifact commit: `ae1a3e5d88318c501055e98d8c6a60702a3e96d4`
- Circuit hash: `42b1ba0b5cbddec8458a9883b01fbeba51f721ad9144345211908a8ae016fc27`
- Shape manifest SHA-256: `4db95076f5caa3640621c4dc9b1b4d2039dfc17f04d0135e256d26640a523e9b`
- Soundness source-tree SHA-256: `c62052a7bc52a26a3c852e54ac53816c41a81c198741b4ff7a08e05dc126fac9`
- Generation-input SHA-256: `00a7186ef92268f84ebf80f4efce625255ade46c8536b405088249683ecc9416`
- Benchmark binary SHA-256: `74b92eb429423bec665e279a48d7e9e6a3ab4dbd6b502c39c583674963ae5c9d`
- Fixed proof envelope: 1,572,910 bytes
- Host: Apple M2 Max, 12 CPU cores, 32 GB RAM
- Runtime: 12 Rayon workers and a 512 MiB minimum stack limit

## Cold desktop samples

Each row is one canonical `proveIdentity` call in a fresh process. Timing was
enabled. The test harness did not run concurrent tests.

| Sample | Prove | Verify | Witness | AIR core | Tree 1 commit | Tree 2 write | Round GKR | STARK prove |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1,221 ms | 42 ms | 74.051 ms | 1,145.134 ms | 120.782 ms | 349.390 ms | 194.225 ms | 378.161 ms |
| 2 | 1,334 ms | 49 ms | 76.041 ms | 1,255.725 ms | 124.641 ms | 351.115 ms | 226.682 ms | 440.694 ms |
| 3 | 1,299 ms | 62 ms | 73.433 ms | 1,223.460 ms | 138.723 ms | 363.549 ms | 210.632 ms | 409.304 ms |
| 4 | 1,258 ms | 50 ms | 75.281 ms | 1,180.245 ms | 113.916 ms | 364.068 ms | 205.281 ms | 392.174 ms |
| 5 | 1,237 ms | 43 ms | 74.230 ms | 1,160.462 ms | 118.796 ms | 357.492 ms | 189.950 ms | 377.437 ms |
| 6 | 1,237 ms | 45 ms | 76.099 ms | 1,158.610 ms | 120.795 ms | 358.153 ms | 197.760 ms | 379.519 ms |
| 7 | 1,385 ms | 48 ms | 76.675 ms | 1,305.838 ms | 119.415 ms | 386.793 ms | 221.861 ms | 471.541 ms |
| **Median** | **1,258 ms** | **48 ms** | **75.281 ms** | **1,180.245 ms** | **120.795 ms** | **358.153 ms** | **205.281 ms** | **392.174 ms** |

The P1 timing-enabled median was 1,362 ms. P3 reduces the canonical median by
104 ms, or 7.6%. It reduces the AIR-core median by 106.201 ms, or 8.3%.

## Verification

- The source-bound artifact drift check passed.
- The live composed proof shape and verification test passed.
- The canonical A1/A2/B unlinkability test passed through `proveIdentity` and
  `verifyIdentity`.

## Pixel 8 result

The phone measurement used the source-bound P3 checkpoint. It ran one cold
release instrumentation test on Firebase model `shiba`, Android API 34.

- Android AAR SHA-256: `491828bff667b0823aa570e291fc8b29d483626bcee917716904f46fc3d341f4`
- Host APK SHA-256: `34044e61f2a4a0749c662040602fe38d44589e050810bc367e1fcc4e459ab448`
- Test APK SHA-256: `8c14464df1017f570d94b6e2cdbb4e00a5851ef5209ff149e22880ebbef45294`
- Fixture SHA-256: `aaa9333b811c162f21ba7d20a6c297fba41f930484a3d2bfa3d2ec1c5d614815`
- Firebase matrix: `matrix-uq2v1lueyszya`
- [Firebase result](https://console.firebase.google.com/project/exploration-dev-417917/testlab/histories/bh.f38b232825a9cbee/matrices/9189940710985295988)

| Metric | P1 | P3 | Change |
| --- | ---: | ---: | ---: |
| Prove | 7,986 ms | 8,101 ms | +115 ms (+1.4%) |
| Verify | 224 ms | 276 ms | +52 ms |
| Witness generation | 505.737 ms | 386.024 ms | -119.713 ms (-23.7%) |
| AIR core | 7,417.405 ms | 7,637.801 ms | +220.396 ms (+3.0%) |
| Peak RSS | 1,989,876 KiB | 1,860,328 KiB | -129,548 KiB (-6.5%) |
| Envelope | 1,638,446 B | 1,572,910 B | -65,536 B (-4.0%) |

The single cold sample is within device-run noise for latency. P3 reduces
witness time, peak memory, the fixed envelope, and committed SHA cells. The
final campaign must measure the selected complete circuit again.
