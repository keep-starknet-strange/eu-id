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
```

`make bench` runs the criterion suite; `make bench-report` writes the JSON.
