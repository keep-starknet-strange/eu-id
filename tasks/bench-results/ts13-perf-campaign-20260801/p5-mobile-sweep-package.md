# P5 mobile runtime sweep

Date: 2026-08-01

Status: complete. The temporary runtime sweep selected the runtime. The final
canonical package passed the desktop, release, and three-phone checks. The
2,000 ms phone prove target failed.

Privacy claim: `public-input unlinkable; transcript zero knowledge pending`

The campaign ran 13 Firebase matrices and 39 phone executions. All executions
called proveIdentity and verifyIdentity. All executions passed. The campaign
selected six Rayon workers, a 2 MiB proof-thread stack, a 16 MiB proof-worker
stack, and no affinity policy.

## Source and package provenance

- Product base: cc7b7e75cedc30fd8cb3ab4f256c3714fc3d68de
- Temporary controls: c35a5213f652474e21ff823bf02dacfffdae2562
- Source-bound artifact: 374f2946
- Mobile fixture: e2e65061
- Temporary circuit hash:
  74a94e63b80143190e5d7969db5fa3203dc462b41d7ce6ac1223650e071acb73
- Proof body capacity: 1,572,864 bytes
- Proof envelope: 1,572,910 bytes
- Firebase project: exploration-dev-503108
- Firebase history: bh.f5f036aa81c4230a
- Result bucket: test-lab-67wdfy26qh61w-j1q1w8tsupf6x
- Package prefix:
  ts13-unlinkable-v1-p5-runtime-sweep-package-20260801-1
- Local evidence root:
  /private/tmp/euid-p5-mobile-sweep-20260801-1/results

Each matrix ran Pixel 8 (shiba), Galaxy S24 Ultra (e3q), and Galaxy A54
(a54x) together on API 34. All matrices used the same two APK objects.

The temporary controls did not add an application API. The SDK exported only
proveIdentity and verifyIdentity. The harness kept each stack setting active
through proof and verification. It restored the process environment only
after verification.

## Temporary sweep SHA-256 values

- Cargo lock:
  23e70c964b943632fed547cfa38e6c1d24cfeac070a3518bc0f1a704f7597dbe
- Rust toolchain file:
  8f0604004d13f7a26332366e59ba731bbb6046aaf789439d760abf67ad78589f
- Generation input:
  60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0
- Shape manifest:
  a5c8c6fdbaac8e1a9b0ca81704b31c7e29f2ec27487f603139531c39faf42d60
- Circuit artifact:
  74a94e63b80143190e5d7969db5fa3203dc462b41d7ce6ac1223650e071acb73
- Generated Rust artifact:
  e28880544aedc980a7177595364307830ac27bcd2ee0f382822e17f875f0d432
- Release probe:
  fb3c5a79564d7c46cfbe1de4c5f416987d6c800c2b2fc9ea8fb6ed445ecf1b5e
- Fixture:
  1adbc93e253c0bc46ec67b9be69c3d953e5f5e1741f08cf221dbcfdb68c41439
- AAR:
  d78d51e199661fd6e23a131d52354b0db3aaf2affc332504c4f52e0487d10738
- Host APK:
  9dd140d9ba9536fa9b8c5c1384217f50398db60f84f88f07e6c17e06e2f49e7f
- Test APK:
  b16b3add76d88907f0c0f44fc48e4fad33dca385d338a50d967f9547ccc1cbb3
- AAR and host APK arm64 library:
  7a3c3b5d49111f5027bd2fa0029be06dcf6d6b4c59077c0d2027f2bc832e36aa

The test APK fixture matched the committed fixture. The host APK arm64
library matched the AAR arm64 library. The library was a stripped AArch64 ELF
shared object. The exact library contained the required NEON instructions.

## Local verification

- The source-bound artifact check passed.
- The release A1/A2/B unlinkability test passed with 12 Rayon workers and one
  test-harness thread.
- The release fixture probe called proveIdentity and verifyIdentity.
- The probe measured 1,117 ms prove and 37 ms verify on the build computer.
- The SDK release tests passed 14 unit tests and two end-to-end tests.
- The Android helper tests passed.
- The fresh Android host and instrumentation sources compiled.
- The independent temporary-control review returned GO.

## Firebase matrix ledger

All links below use Firebase history bh.f5f036aa81c4230a.

| No. | Configuration | Matrix | Numeric ID | Result directory |
| ---: | --- | --- | ---: | --- |
| 1 | w6-t64-s64 | matrix-9pzjabtr7iffa | [5276840698474475873](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/5276840698474475873) | ts13-unlinkable-v1-p5-w6-t64-s64-20260801-1 |
| 2 | w4-t64-s64 | matrix-2yzeyvqoyt7ml | [7752097377956898397](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/7752097377956898397) | ts13-unlinkable-v1-p5-w4-t64-s64-20260801-1 |
| 3 | w8-t64-s64 | matrix-1hq9kbfwmnxt4 | [8739188903502062494](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/8739188903502062494) | ts13-unlinkable-v1-p5-w8-t64-s64-20260801-1 |
| 4 | w6-t64-s48 | matrix-azrwc5wm4fqja | [4612885942414202963](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/4612885942414202963) | ts13-unlinkable-v1-p5-w6-t64-s48-20260801-1 |
| 5 | w6-t64-s32 | matrix-3mspa1qkun7mw | [6314452890086908594](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/6314452890086908594) | ts13-unlinkable-v1-p5-w6-t64-s32-20260801-1 |
| 6 | w6-t64-s24 | matrix-2v5ze2ieoxc0s | [8047706642342527959](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/8047706642342527959) | ts13-unlinkable-v1-p5-w6-t64-s24-20260801-1 |
| 7 | w6-t64-s16 | matrix-1sqlxji39g9lt | [6717055808755343026](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/6717055808755343026) | ts13-unlinkable-v1-p5-w6-t64-s16-20260801-1 |
| 8 | w6-t8-s16 | matrix-323evav2j74zx | [7264971820180686360](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/7264971820180686360) | ts13-unlinkable-v1-p5-w6-t8-s16-20260801-1 |
| 9 | w6-t2-s16 | matrix-3lgqzjsuk88e0 | [7498585318246171736](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/7498585318246171736) | ts13-unlinkable-v1-p5-w6-t2-s16-20260801-1 |
| 10 | affinity A1 | matrix-3ampoc2hhfk53 | [4822421344022860443](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/4822421344022860443) | ts13-unlinkable-v1-p5-affinity-a1-w6-t2-s16-20260801-1 |
| 11 | affinity B1 | matrix-2vwnao9wvlxn2 | [7685274511497690343](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/7685274511497690343) | ts13-unlinkable-v1-p5-affinity-b1-w6-t2-s16-20260801-1 |
| 12 | affinity B2 | matrix-2my2cwk01pdid | [7490016446522745792](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/7490016446522745792) | ts13-unlinkable-v1-p5-affinity-b2-w6-t2-s16-20260801-1 |
| 13 | affinity A2 | matrix-286d5ppmalk0s | [5748889457052606457](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/5748889457052606457) | ts13-unlinkable-v1-p5-affinity-a2-w6-t2-s16-20260801-1 |

## Validation invariants

All 39 executions met these conditions:

- The instrumentation result was OK (1 test) with code -1.
- The circuit hash was
  74a94e63b80143190e5d7969db5fa3203dc462b41d7ce6ac1223650e071acb73.
- The envelope was exactly 1,572,910 bytes.
- The summary contained the requested, configured, and actual worker values.
- The summary contained the requested and configured stack values.
- stack_environment_covered_verify was true.
- The harness wrote one summary and 25 phase records.
- The phase indices were exactly 0 through 24.
- Each phase record contained phase_count 25.
- Verification was at most 330 ms.
- No benchmark process had a crash, OOM, fatal signal, stack overflow, or ANR.

Some device logs contained unrelated Android system errors. Their process
identifiers and package names did not match the benchmark process.

## Exact 39-run results

Each result cell is prove / verify / peak HWM. Times are milliseconds. Peak
HWM is KiB. In each configuration name, w is the requested worker count, t is
the proof-thread stack in MiB, and s is the proof-worker stack in MiB.

### Worker count and worker stack

| Configuration | Pixel 8 | Galaxy S24 Ultra | Galaxy A54 |
| --- | ---: | ---: | ---: |
| w6-t64-s64 | 5,230 / 258 / 1,347,124 | 3,174 / 157 / 1,379,940 | 5,860 / 222 / 1,339,028 |
| w4-t64-s64 | 5,309 / 244 / 1,343,360 | 3,813 / 203 / 1,372,184 | 5,667 / 217 / 1,333,744 |
| w8-t64-s64 | 5,386 / 223 / 1,346,416 | 4,602 / 233 / 1,377,888 | 6,289 / 235 / 1,344,696 |
| w6-t64-s48 | 4,986 / 232 / 1,345,488 | 2,739 / 140 / 1,378,108 | 6,479 / 194 / 1,338,104 |
| w6-t64-s32 | 5,539 / 228 / 1,345,352 | 2,618 / 130 / 1,420,800 | 6,262 / 287 / 1,335,840 |
| w6-t64-s24 | 6,680 / 297 / 1,344,456 | 2,692 / 161 / 1,412,928 | 5,766 / 290 / 1,339,988 |
| w6-t64-s16 | 7,590 / 261 / 1,345,648 | 3,473 / 160 / 1,370,104 | 5,894 / 233 / 1,343,316 |

Six workers were faster than four and eight workers on Pixel 8 and Galaxy S24
Ultra. Four workers were 193 ms faster than six workers on Galaxy A54, but
they were 79 ms slower on Pixel 8 and 639 ms slower on Galaxy S24 Ultra.
Eight workers were slower on all three phones. The campaign kept six workers
because neither four nor eight workers improved all three binding phones.
This result is not a statistical optimum. Each row contains one cold sample
per phone.

All five worker-stack sizes passed on all three phones. The fixed rule selected
the smallest passing size. The selected proof-worker stack is 16 MiB. The
single cold-run latency changed between rows, but peak HWM did not change in
proportion to the stack reservation.

### Proof-thread stack

| Configuration | Pixel 8 | Galaxy S24 Ultra | Galaxy A54 |
| --- | ---: | ---: | ---: |
| w6-t8-s16 | 5,746 / 239 / 1,344,296 | 3,715 / 183 / 1,374,916 | 7,146 / 330 / 1,336,876 |
| w6-t2-s16 | 5,507 / 195 / 1,345,840 | 3,725 / 184 / 1,371,252 | 6,928 / 272 / 1,337,892 |

Both reduced proof-thread stack sizes passed on all three phones. The fixed
rule selected the smallest passing size. The selected proof-thread stack is
2 MiB.

### Affinity A/B/B/A

A rows used six workers and no affinity request. B rows requested
exclude_min_cluster. In B rows, the configured worker count came from the
selected CPU mask.

| Row | Pixel 8 | Galaxy S24 Ultra | Galaxy A54 |
| --- | ---: | ---: | ---: |
| A1 | 6,138 / 215 / 1,346,348 | 4,309 / 219 / 1,379,092 | 6,459 / 230 / 1,340,420 |
| B1 | 5,143 / 192 / 1,345,084 | 3,012 / 129 / 1,418,580 | 6,290 / 240 / 1,337,220 |
| B2 | 5,196 / 225 / 1,344,108 | 2,752 / 121 / 1,416,604 | 5,638 / 177 / 1,333,964 |
| A2 | 8,069 / 268 / 1,347,308 | 2,898 / 156 / 1,416,248 | 6,137 / 224 / 1,340,456 |

The B policy used the cpu_capacity topology source. It applied without a
fallback:

| Phone | Workers requested / configured / actual | Selected and effective CPUs | Excluded CPUs |
| --- | --- | --- | --- |
| Pixel 8 | 6 / 4 / 4 | 4-7 | 0-3 |
| Galaxy S24 Ultra | 6 / 5 / 5 | 2-6 | 0-1 |
| Galaxy A54 | 6 / 4 / 4 | 4-7 | 0-2 |

The selected mask removed the minimum-capacity cluster from the CPU mask that
Firebase allowed. The selected mask matched the effective mask and the
allowed-during mask.

## Affinity decision

The fixed rule used these values:

- A mean = (A1 + A2) / 2.
- B mean = (B1 + B2) / 2.
- A spread = absolute value of A1 - A2.
- B spread = absolute value of B1 - B2.
- Threshold = maximum of the A spread and B spread.
- Pixel 8 and Galaxy S24 Ultra passed only if A mean - B mean was greater
  than the threshold.
- Galaxy A54 passed if B mean was not greater than A mean + threshold.

| Phone | A mean | B mean | Improvement | A spread | B spread | Threshold | Result |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| Pixel 8 | 7,103.5 | 5,169.5 | 1,934 | 1,931 | 53 | 1,931 | Pass by 3 ms |
| Galaxy S24 Ultra | 3,603.5 | 2,882 | 721.5 | 1,411 | 260 | 1,411 | Fail |
| Galaxy A54 | 6,298 | 5,964 | 334 | 322 | 652 | 652 | Pass no-regression rule |

The policy did not meet the full rule because Galaxy S24 Ultra failed. The
campaign rejected affinity. The final selected runtime has no affinity policy.

## Selected runtime

- Requested, configured, and actual Rayon workers: 6
- Proof-thread stack: 2 MiB
- Proof-worker stack: 16 MiB
- Affinity policy: none
- Allocator: system allocator
- AArch64 acceleration: existing NEON path

The 16 MiB worker stack and 2 MiB proof-thread stack are the smallest tested
sizes that passed proof and verification on all three phones. The canonical
product sets these values in one fixed proof runtime. The product has no
temporary runtime controls.

## P4 comparison

The comparison uses the mean of the two fresh no-affinity A rows. It compares
the same selected P4 PCS point before and after the accepted P5 memory changes.
Each result cell is prove / verify / peak HWM.

| Phone | P4 selected point | P5 A-row mean | Prove change | Peak HWM change |
| --- | ---: | ---: | ---: | ---: |
| Pixel 8 | 5,664 / 218 / 1,646,140 | 7,103.5 / 241.5 / 1,346,828 | +25.4% | -299,312 KiB (-18.2%) |
| Galaxy S24 Ultra | 3,884 / 126 / 1,744,896 | 3,603.5 / 187.5 / 1,397,670 | -7.2% | -347,226 KiB (-19.9%) |
| Galaxy A54 | 6,062 / 202 / 1,643,952 | 6,298 / 227 / 1,340,438 | +3.9% | -303,514 KiB (-18.5%) |

The P5 changes reduced peak HWM by 292 MiB to 339 MiB on the binding phones.
The cold proving results had high run-to-run variation. They do not show a
stable proving-time improvement. The first selected-runtime checkpoint was
5,507 ms on Pixel 8, 3,725 ms on Galaxy S24 Ultra, and 6,928 ms on Galaxy A54.
The fresh A-row means above give the paired no-affinity comparison.

## Gate status

The envelope and verification gates passed. Every execution used a fixed
1,572,910-byte envelope. The maximum verification time was 330 ms.

The 2,000 ms cold-prove gate failed on every phone. Even the fastest measured
row for each phone was above the gate:

| Phone | Fastest measured prove | Configuration | Distance above 2,000 ms |
| --- | ---: | --- | ---: |
| Pixel 8 | 4,986 ms | w6-t64-s48 | 2,986 ms |
| Galaxy S24 Ultra | 2,618 ms | w6-t64-s32 | 618 ms |
| Galaxy A54 | 5,638 ms | affinity B2 | 3,638 ms |

The Galaxy A54 minimum came from the rejected affinity policy. Thus, these
minimum values are not a proposed final configuration. No measured
configuration met the 2,000 ms gate.

## Original P5 canonical product evidence

The final product uses one fixed runtime and the `proveIdentity` and
`verifyIdentity` API. It has this provenance:

- Soundness-source checkpoint: `13a1a51d`
- Source-bound artifact commit: `a34ac578`
- Final package source and mobile fixture commit: `a91085dc`
- Circuit hash:
  `2eff9e073151b4bce733516f4b6dd411b6d48ef5425fd93d41c64bedf524fea9`
- Proof envelope: 1,572,910 bytes

The final package 3 files have these SHA-256 values:

- AAR:
  `cdd744130c540f8ba910843b2a0fafe482714b864c200c06ee375c7aa6f242fa`
- Host APK:
  `b126d7693abb8079b2412a0ba1590124f16252ed61449d96e0b86f5aec3e6766`
- Test APK:
  `050ddfca27695d32c1c6e1d563ec76a1f16ad2d9551f497e877e5cd839678ae3`
- Fixture:
  `c9fe96c76b13a884afb324e68dd939561c8d4664fe59e8cdfc85e8bf0625ea52`
- AAR and host APK arm64 library:
  `aedf9b1e6213e6d0bc7bf5b2cd20e51a5908eee5cee844b7e11bbcf87533dc38`

The final serial desktop campaign ran seven samples. The median prove time was
1,162 ms. The median verify time was 17 ms. The first verify time was 42 ms.
The envelope was 1,572,910 bytes.

The final Firebase run used matrix `matrix-92u1aei93c81a`, numeric ID
[4904946063125125660](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f5f036aa81c4230a/matrices/4904946063125125660),
and history `bh.f5f036aa81c4230a`. One matrix ran the same package on all
three phones with API 34.

| Phone | Prove | Verify | Peak HWM |
| --- | ---: | ---: | ---: |
| Pixel 8 | 5,450 ms | 239 ms | 1,346,468 KiB |
| Galaxy S24 Ultra | 2,755 ms | 140 ms | 1,414,276 KiB |
| Galaxy A54 | 5,853 ms | 255 ms | 1,338,168 KiB |

Each execution reported six actual Rayon workers, a 2,097,152-byte
proof-thread stack, a 16,777,216-byte proof-worker stack, 25 phase records,
and a 1,572,910-byte envelope. Each execution returned `OK (1 test)`. No
execution had an OOM, crash, or ANR.

All normal release workspace tests passed. All 18 ignored release tests
passed. Release Clippy passed with warnings denied. Formatting, the release
build for all targets, the quantum-only dependency check, the source-bound
artifact check, and the diff check passed.

The final package passed the 350 ms verification gate and the 2,500,000-byte
envelope ceiling. It failed the 2,000 ms prove target on all three phones. P6
was infeasible in the fixed campaign scope, so the campaign skipped it.

## Restored canonical state — 2026-08-02

A-018 restored P5 after c7 failed the phone-throughput gate. The source bytes
match the last sound P5 path. The source-bound commit changed, so the circuit
hash also changed.

- Measured source, artifact, and fixture commit:
  `cdfdf52c38a86143733ea80e4e8a3064a53950f9`.
- Source restore commit:
  `1e035312a566a2b8b96f4febad7eb35f17bed493`.
- Circuit and artifact SHA-256:
  `6b30e79449d331477027412fd30c831f7bb45cea42214b072845173fea0241b6`.
- Soundness-source-tree SHA-256:
  `a39bc90c4c14226728bfd4f4a314a12a81f162c8fd62991fc5f214973de99ec3`.
- Shape-manifest SHA-256:
  `a5c8c6fdbaac8e1a9b0ca81704b31c7e29f2ec27487f603139531c39faf42d60`.
- Generation-input SHA-256:
  `60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0`.
- Binary SHA-256:
  `3760907c6c4754e1941b4ea8dd61dc589a4a2df62f6f7b0b57af571906f8145a`.
- Mobile-fixture SHA-256:
  `06ef4ade577e1b69a776adafa778fd0fe16e3c75478772f1d5abf0c7072a98f4`.
- Cargo.lock SHA-256:
  `23e70c964b943632fed547cfa38e6c1d24cfeac070a3518bc0f1a704f7597dbe`.
- Rust toolchain file SHA-256:
  `8f0604004d13f7a26332366e59ba731bbb6046aaf789439d760abf67ad78589f`.
- Proof-body capacity: 1,572,864 bytes.
- Identity-proof envelope: 1,572,910 bytes.

The PCS uses proof-of-work 20, blowup log 3, 36 queries, last-layer log 1,
fold step 2, and lifting log 19. The six workspace packages used their default
feature sets.

### Fresh-process desktop record

The host was a 12-core Apple M2 Max MacBook Pro with 32 GB of memory. It ran
macOS 26.5.2, build 25F84. The compiler was Rust nightly 1.94.0 from
2026-01-14. One fresh release process made one `proveIdentity` call and one
`verifyIdentity` call.

| Metric | Result |
| --- | ---: |
| `proveIdentity` | 1,280 ms |
| `verifyIdentity`, first and median | 42 ms |
| Maximum resident set size | 1,513,652,224 bytes |
| Proof-body capacity | 1,572,864 bytes |
| Envelope | 1,572,910 bytes |
| Phase rows | 25 |
| Actual proof workers | 6 |
| Proof-thread stack | 2,097,152 bytes |
| Worker stack | 16,777,216 bytes |

The historical matrix `matrix-92u1aei93c81a` remains the A-018 phone-latency
baseline. It used the prior P5 circuit hash
`2eff9e073151b4bce733516f4b6dd411b6d48ef5425fd93d41c64bedf524fea9`.
It is same-path latency evidence, not current-hash evidence.
