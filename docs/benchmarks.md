# eu-id Combined-Prover Benchmarks

Honest end-to-end performance numbers for the combined, cross-bound identity
proof (P256 ECDSA + SHA-256 + digest-bind bridge + age + nationality), with a
per-component breakdown so the cost drivers are explicit. These are the numbers
the POC's performance argument rests on.

> **Machine-readable results** live in [`benchmarks/`](./benchmarks/):
> [`laptop-m4max.json`](./benchmarks/laptop-m4max.json) (single-threaded
> baseline), [`laptop-m4max-parallel.json`](./benchmarks/laptop-m4max-parallel.json)
> (Stwo rayon paths on), and [`mobile-devices.json`](./benchmarks/mobile-devices.json)
> (on-device, to be filled in from device runs).

## How the numbers are produced

Two harnesses, both driving the **same** per-stage proving paths
(`crates/eu-id-prover/benches/common/stages.rs`):

- **Timing** — a criterion benchmark, `crates/eu-id-prover/benches/identity_bench.rs`.
  Statistically rigorous prove/verify wall-clock for each stage. All inputs
  (witnesses, the P256 draft) are built once, outside the measured window, so
  each benchmark times only the STARK prove/verify.
- **Memory + size + machine-readable JSON** — a report driver,
  `crates/eu-id-prover/examples/bench_report.rs`. Per stage it records median
  prove/verify, peak memory, and serialized proof size, then emits the JSON
  results and a comparison.

**Peak memory** is sampled as mach `phys_footprint` (the figure iOS jetsam
enforces) by a background thread polling at a fixed cadence — the same crate and
metric the FFI / mobile harness uses, so laptop and device peaks come from one
method. Because `phys_footprint` is process-global and the allocator does not
return freed pages to the OS, the report driver measures **each stage in its own
process**; otherwise a tiny predicate would inherit the earlier high-water mark
and falsely report gigabytes.

**Stages.** `p256`, `sha`, `age`, `nat` are the standalone components.
`pipeline` is the full five-module combined STARK with the witness pre-built (the
honest per-component cost attribution). `pipeline_e2e` is the relying-party path
(`prove_identity` → `verify_identity`), which additionally builds the witness +
P256 draft and signs — the figure the on-device harness reproduces. The SHA stage
runs at the **same group width the combined proof uses** (`W = 6`; see the cost
note below), so the per-component number reconciles with the pipeline.

## Laptop results — Apple M4 Max (14 cores, 36 GB), single-threaded

Single-threaded is the honest baseline (see the parallel note below). Medians;
peak is mach `phys_footprint`.

| stage          | prove   | verify | peak      | proof size |
|----------------|--------:|-------:|----------:|-----------:|
| p256           | 0.71 s  |  36 ms | 1.61 GiB  |   3.22 MiB |
| sha (W=6)      | 0.43 s  |  15 ms | 0.75 GiB  |   0.76 MiB |
| age            | 0.01 s  | 0.14 ms|  44 MiB   |  12.4 KiB  |
| nat            | 0.002 s | 0.04 ms|  41 MiB   |   3.3 KiB  |
| **pipeline**   | **1.03 s** | **51 ms** | **1.60 GiB** | **7.48 MiB** |
| pipeline_e2e   | 1.27 s  |  50 ms | 1.66 GiB  |   7.48 MiB |

(criterion confirms the timing to tight intervals: p256 prove 694 ms, sha
434 ms, pipeline 984 ms; the sub-millisecond predicate verifies are 138 µs / 44 µs.)

### Cost attribution — P256 dominates (after the W=6 fix)

The combined STARK prove (≈1.0 s) breaks down as **P256 ≈ 68%, SHA ≈ 30%,
predicates < 1%**, with the small remainder the bridge + shared FRI. P256 is the
cost driver, as expected.

This was **not** the first reading, and the difference is the most useful finding
here. The combined prover originally ran SHA at group width **W=7** (`2^21`-row
Maj/Ch table). At W=7 the picture inverted: SHA proved in **1.26 s** at **3.19 GiB**
peak — *larger than P256* — and the combined proof took **1.94 s** at **6.39 GiB**
peak (over 4× the iOS jetsam budget). Group width is purely the round-function
table packing — orthogonal to the message schedule, the digest binding, and the
field-exposure windows — and `W = 6` (the `2^18`-row table, the legal minimum) is
strictly cheaper for the single-block credential. Switching to W=6:

| | W=7 (before) | W=6 (now) | change |
|---|--:|--:|--:|
| SHA prove / peak        | 1.26 s / 3.19 GiB | 0.43 s / 0.75 GiB | ~3× / ~4× smaller |
| combined STARK prove    | 1.94 s            | 1.03 s            | ~2× faster |
| combined peak           | 6.39 GiB          | 1.60 GiB          | ~3.5× smaller |
| end-to-end prove        | 2.23 s            | 1.27 s            | ~1.8× faster |

The full soundness + relying-party suite (all mutation classes reject, the
boundary positives verify, the API round-trips) passes at **both** widths, so the
switch is a free correctness-preserving win. The combined prover now uses W=6
(`generator::SHA_GROUP_WIDTH`).

### Proof size and verify

The combined proof is **~7.5 MiB** and verifies in **~50 ms**. P256 is the bulk of
the size (3.2 MiB); SHA adds 0.76 MiB; the predicates are negligible (KiB). Verify
is fast across the board.

### End-to-end vs the per-stage sum

`pipeline_e2e` (1.27 s) ≈ the combined STARK (1.03 s) + ~0.25 s of witness + P256
draft generation and signing. The per-component sum (p256 + sha + age + nat ≈
1.15 s) is close to the combined STARK (1.03 s): the shared single proof neither
saves nor costs much over running the components back to back — each component's
trace generation dominates its own cost and the shared FRI is a small fraction.

### Multi-threading (parallel) delta — negligible

Building with `--features parallel` (Stwo's rayon paths) does **not** meaningfully
move these numbers on the M4 Max: combined prove 1.03 s → 0.98 s, SHA 0.43 s →
0.41 s (within noise). P256, now ~70% of the cost, has no rayon path at all, so
the honest baseline is single-threaded and `parallel` is not currently a lever for
the combined proof. (See `laptop-m4max-parallel.json` for the full parallel run.)

## Memory and the mobile budget

The laptop peak for the combined proof is now **~1.6 GiB** (down from ~6.4 GiB at
W=7). This is the **Mac's** `phys_footprint`, which over-reports relative to a
device — macOS and the iOS simulator share the Darwin kernel, and both report the
host Mac's footprint, not a phone's. It is **not** a device number. At W=7 the
combined proof was ~4× over the iOS jetsam budget (~1.3–1.5 GB) on the laptop
footprint alone — a clear scope risk; the W=6 switch brings it down, and the
on-device run (below) **confirms it fits**: **~1.29 GiB on an iPhone 15 Pro Max,
no jetsam**.

## Mobile — on-device harness

The combined prover is exposed to the SwiftUI harness (`mobile/EuIdBench`) via the
C ABI `eu_id_bench_identity`, which builds a credential + policy, signs with the
demo issuer, and runs `prove_identity` → `verify_identity` under the same
peak-`phys_footprint` sampler — measured entirely inside Rust so FFI/UI overhead
stays out of the window. The app's **Prove identity** button (and the
`--autorun-identity` launch argument, for headless capture) drive it; results are
emitted to the unified log as a grep-friendly `RESULT label=identity …` line.

**Device measurement — iPhone 15 Pro Max (A17 Pro, 8 GB, iOS 26.5).** The combined
proof proves *and* verifies on the phone (`ok=1`): **prove ≈ 1.81 s, verify ≈ 45 ms,
peak `phys_footprint` ≈ 1.29 GiB, proof 7.48 MiB** (single run via the
`--autorun-identity` launch path; built + deployed with `xcodebuild` +
`devicectl`). It ran clean — no jetsam. The A17 Pro is ~1.4× the M4 Max
single-threaded (1.81 s vs the laptop's 1.27 s), as expected, and the device peak
(1.29 GiB) is *below* the laptop's Mac-footprint reading (1.66 GiB), confirming the
laptop over-reports. Recorded in
[`benchmarks/mobile-devices.json`](./benchmarks/mobile-devices.json).

**This is where the W=6 switch earns its keep.** At W=7 the SHA component alone
peaked at ~3.2 GiB, so the combined proof would not have fit a phone's memory; at
W=6 it lands at ~1.29 GiB — comfortable on the 8 GB Pro Max (where it ran clean),
and in the neighborhood of the ~1.3–1.5 GB limit a 3–4 GB floor device would
enforce. (Before the device run, the iOS simulator served as the wiring gate —
W=6 sim: `ok=1`, ~1.27 s, host footprint — but the device numbers above are the
real ones.)

**Harness fix surfaced by the validation.** The combined prover overflows the
512 KB default stack of a `DispatchQueue` worker thread (it faults with
`EXC_BAD_ACCESS` at the stack guard page — the SHA-only prover fit, the
P256-heavy combined one does not). The harness therefore runs each prove on a
dedicated `Thread` with a 32 MB stack (`ContentView.onLargeStack`). This applies
on device too, so it is a prerequisite for any on-device run, not a
simulator-only quirk.

### Reproduce on a device

```bash
# Build the xcframework (device + simulator slices):
crates/eu-id-ffi/build-xcframework.sh

# Generate the harness project (set your Apple Team ID for on-device signing):
cd mobile/EuIdBench && DEVELOPMENT_TEAM=<team-id> xcodegen generate

# Device (automatic signing; phone unlocked):
xcodebuild -project EuIdBench.xcodeproj -scheme EuIdBench -configuration Release \
  -destination 'generic/platform=iOS' -derivedDataPath build-device \
  -allowProvisioningUpdates build
DEV=<device-udid>; APP=build-device/Build/Products/Release-iphoneos/EuIdBench.app
xcrun devicectl device install app --device "$DEV" "$APP"
xcrun devicectl device process launch --device "$DEV" co.starkware.euid.bench
# Tap "Prove identity" and read the numbers (or stream the device log for the
# `EUIDBENCH RESULT label=identity` line).
```

## Proof-size byte-breakdown (Phase 10 baseline, §10.1)

Phase 10 is about shrinking the multi-MB combined proof (the Bluetooth transfer
bottleneck). Before optimising, we decomposed the proof into its serialized
parts so every later task is prioritised against real numbers. The breakdown
driver (`BENCH_BREAKDOWN=1 … bench_report`) proves the combined pipeline once,
sizes each `CommitmentSchemeProof` field with `bincode::serialized_size`,
attributes the width-linear streams per module by committed-column count, and
records the real bzip2 transport size. Machine-readable results:
[`benchmarks/proof-size-breakdown.json`](./benchmarks/proof-size-breakdown.json).

**Headline:** the combined proof is **7,300,513 bytes (6.96 MiB)** raw bincode,
**4.34 MiB** over the wire (bzip2-best, **1.60×**). It is **~96.6% width-linear**
(opened column values + OODS), only **~3.4% depth** (FRI + Merkle auth paths).
And — the surprise — **SHA-256, not P256, is the single largest contributor to
proof size** (62% of the width-linear mass), the inverse of the prove-time and
standalone-size picture where P256 dominates.

### By `CommitmentSchemeProof` field (inner `stark_proof` = 6.96 MiB)

| field            | size      | %     | nature |
|------------------|----------:|------:|--------|
| `queried_values` | 6.06 MiB  | 87.1% | opened column values — **width × queries** |
| `sampled_values` (OODS) | 672.7 KiB | 9.4% | mask evaluations — width-linear |
| `fri_proof`      | 154.8 KiB | 2.2%  | FRI layer commitments + witnesses — **depth** |
| `decommitments`  | 90.4 KiB  | 1.3%  | Merkle auth-path hashes — **depth** |
| `commitments`    | 136 B     | 0.0%  | per-tree Merkle roots |
| `proof_of_work`  | 8 B       | 0.0%  | grinding nonce |
| `config`         | 25 B      | 0.0%  | `PcsConfig` |

The two width-linear streams (`queried_values` + OODS) are **96.6%** of the
proof; the two depth-driven streams (`fri_proof` + `decommitments`) are **3.4%**.
So the size levers are **query count** (§10.2 — scales the whole 96.6%) and
**committed width** (§10.5/§10.6); reducing FRI depth can recover at most ~245 KiB
total.

### Per-module attribution of the width-linear bytes

The proof commits **28,383 columns** across four trees (311 preprocessed +
16,976 trace + 11,088 interaction + 8 composition), every one opened at the
P256-inherited **54 queries** (`FriConfig::new(5, 2, 54, 1)`, `log_blowup = 2`).
Attributing `queried_values` + OODS by each module's committed-column count:

| module | columns (pre / trace / interaction) | width-linear | % |
|--------|------------------------------------:|-------------:|---:|
| **sha**    | 17,601 (85 / 9,940 / 7,576) | **4.17 MiB** | **62.0%** |
| **p256**   | 10,463 (216 / 6,927 / 3,320) | **2.48 MiB** | **36.9%** |
| bridge | 229 (2 / 87 / 140) | 55.6 KiB | 0.8% |
| age    | 64 (7 / 17 / 40) | 15.5 KiB | 0.2% |
| nat    | 18 (1 / 5 / 12) | 4.4 KiB | 0.1% |
| composition (shared) | 8 | ~2 KiB | 0.0% |

**SHA dominates because it is the widest module, and width is what proof size is
linear in.** Its 9,940 trace columns alone account for ~2.0 MiB of opened values
(confirming the roadmap's ~2 MiB / 9,909-column estimate — the 31-column delta is
the §6.5–§6.7 credential-binding tail), but its **7,576 LogUp interaction
columns add a further ~2.2 MiB the estimate missed**. Crucially, standalone SHA
proves under the weak `PcsConfig::default()` (few queries), so its standalone
proof (0.76 MiB) **drastically understates** its footprint inside the combined
proof, where it inherits P256's 54-query / `log_blowup = 2` config. This flips
the roadmap's stated priority: **§10.5 (shrink SHA width, including the
interaction tree) is the higher-value structural lever, not §10.6 (P256).**

**P256 is width-bound, not depth-bound.** Its 2.48 MiB is almost entirely opened
values + OODS; the depth streams (FRI + decommitments) total only **245 KiB
across all modules combined**. So §10.6's depth lever (shorter FRI chain via a
smaller `log_size`) can recover at most ~245 KiB; only the width lever (limb-slot
reuse across mutually-exclusive row types) is a meaningful P256 size play — and it
is secondary to SHA.

### Merkle auth-path sharing — already deduplicated (§10.3 / §10.1 req)

Stwo's `MerkleDecommitmentLifted` **already shares upper auth-path nodes across
co-located queries** — no "octopus" decommitment work remains. The lifted Merkle
verifier (`stwo/src/core/vcs_lifted/verifier.rs::verify`) walks the tree
bottom-up, chunks each layer by siblings (`a.idx ^ 1 == b.idx`), and consumes a
witness hash **only when a node's sibling is absent** (chunk length 1); where two
query paths converge, the shared ancestor is computed once and never re-sent. The
tiny `decommitments` field (90.4 KiB, 1.3%) is consistent with already-deduped
paths. **§10.3's batched/"octopus" decommitment item can be closed as
already-implemented upstream.**

### Compression is not the lever

bzip2-best yields only **1.60×** (6.96 MiB → 4.34 MiB). STARK proofs are
high-entropy — Merkle digests are incompressible and `queried_values` is densely
packed field elements — so the wire payload stays multi-MB regardless. The real
reductions come from committing fewer/narrower values (§10.2, §10.5) or
collapsing the whole proof via recursion (§10.4), not from a better compressor.
The §10.3 31-bit M31 bit-packing (~3% of the width-linear mass) is marginal but
free; it stacks on top.

### Baseline note — the proof already shrank ~7% on this branch

§7.2 recorded the combined proof at **7,846,609 B (7.48 MiB)**. The current
baseline is **7,300,513 B (6.96 MiB)**, a ~7% reduction from the LogUp
pair-batching landed in commit `4dc2e56` ("Batch eligible LogUp columns in
pairs"), which halves eligible interaction columns. The numbers above are the
**post-batching** Phase-10 baseline; later tasks measure against them.

## Reproduce the laptop numbers

```bash
# Statistical timing (per-stage + full):
cargo bench -p eu-id-prover

# Memory + size + machine-readable JSON (single-threaded baseline):
BENCH_LABEL=m4max-single cargo run --release -p eu-id-prover --example bench_report \
    -- docs/benchmarks/laptop-m4max.json

# Parallel delta:
BENCH_LABEL=m4max-parallel cargo run --release -p eu-id-prover --example bench_report \
    --features parallel -- docs/benchmarks/laptop-m4max-parallel.json

# Proof-size byte-breakdown (Phase 10 baseline, §10.1):
BENCH_BREAKDOWN=1 BENCH_LABEL=m4max cargo run --release -p eu-id-prover \
    --example bench_report -- docs/benchmarks/proof-size-breakdown.json
```

`make bench` runs the criterion suite; `make bench-report` writes the JSON.
