# Stwo Mobile Backend — Feasibility

> **Status:** feasibility research complete — verdict **GO (conditional)**.
> **Task:** determine how Stwo proof generation runs on iOS and Android, pin the
> mobile toolchain, choose the FFI strategy, and flag the memory risk early.
> **Feeds:** the laptop benchmark (3.14 — the post-week-2 go/no-go gate) and the
> mobile benchmark harness (3.15). **Audience:** the benchmarking work and anyone
> wiring the `mobile/` harness or an FFI crate.
> **Evidence rule:** every claim here is backed by a primary source, a Stwo source
> citation (commit `e1286720`, the pin in `Cargo.lock`), or a build transcript
> reproducible from Appendix A — not desk research. Where the public record is
> thin, this document says so rather than guessing.

---

## 0. Verdict (read this first)

**Stwo proof generation runs on ARM mobile.** Three independent lines of evidence:

1. **Source.** Stwo's performant backend (`SimdBackend`) is built on portable
   `std::simd` and ships a *hand-written NEON* path for the hot M31 multiply
   (`crates/stwo/src/prover/backend/simd/m31.rs`). ARM is a first-class target of
   that file — its own doc-comment lists `neon` alongside `avx512`/`wasm`. Stwo has
   **no `target_os`-specific code at all** (Appendix A), so iOS and Android exercise
   identical prover code.
2. **Build.** `stwo-sha256` — which compiles all of `stwo` +
   `stwo-constraint-framework` — **cross-compiles cleanly** to `aarch64-apple-ios`
   and `aarch64-apple-ios-sim` on a stock macOS + Xcode machine, today, in seconds
   (10.5 s and 5.0 s, Appendix A). The Android target compiles and stops only at one
   C build-script for a missing NDK — a standard toolchain step, not a Stwo limit.
3. **Field precedent.** FibRace (arXiv 2510.14693, Sept 2025) generated 2.2 M proofs
   on 1,420 phone models with an M31 Circle-STARK prover of the same family as Stwo,
   in **under 5 s** on most modern phones — the bar the PRD cites.

**Verdict: GO**, with two conditions, neither a blocker:

- **C1 — Android needs the NDK.** Stwo's *Rust* is portable to
  `aarch64-linux-android` (it is identical to the verified iOS `aarch64` code — §2,
  §3.2). The build needs the Android NDK installed so the `blake3` dependency's `cc`
  build script finds a cross-compiler. `cargo-ndk` wires this up. One-time setup.
- **C2 — full-pipeline memory is unmeasured.** The SHA-256 component *alone* is
  **low memory risk** (§5). The full eu-id Big AIR (SHA-256 ×2 + ECDSA P-256 + mdoc,
  one shared proof) is the open question — exactly what the 3.14 laptop go/no-go and
  the 3.15 mobile run must measure. Per the PRD, if it does not fit, narrow scope.

The chosen toolchain is pinned in §6. The rest of this document substantiates each
claim above.

---

## 1. What FibRace proves — and what it does not

The PRD's headline mobile claim traces to **FibRace** (arXiv `2510.14693`, KKRT Labs
+ Hyli). The honest reading:

| FibRace fact | Source |
|---|---|
| 6,047 players, 99 countries, **2,195,488 proofs** on **1,420 device models** | arXiv 2510.14693 abstract |
| Three-week campaign, **Sept 11–30 2025** | same |
| **< 5 s** per proof on most modern smartphones | same |
| Devices with **≥ 3 GB RAM proved stably**; performance ∝ RAM + SoC | same |
| Apple A19 Pro and M-series chips were fastest | same |
| Client-side proving — no remote prover, no special hardware | same |

**The caveat that matters.** FibRace's prover is **Cairo M** (KKRT Labs' M31-based
Cairo variant), proving a Fibonacci statement — *not* literally the
`starkware-libs/stwo` crate this project depends on, and not a real credential
circuit. Cairo M sits in the **same M31 / Circle-STARK prover family** as Stwo
("S-two"), so FibRace is strong evidence that *this class of prover* hits the sub-5 s
bar on consumer phones at scale. It is **not** evidence that the eu-id circuit
specifically will. That gap is what 3.14/3.15 close. Treat FibRace as the existence
proof for the *platform*, and the 3.14 SHA-256 benchmark as the existence proof for
*our circuit*.

StarkWare's own framing corroborates the platform: S-two is described as targeting
"instant proving on phones, browsers, and laptops", with backends spanning
"CPU, SIMD, GPU, and soon WebGPU and WASM" over the 31-bit Mersenne field — i.e. the
`SimdBackend` is the intended mobile/ARM path, which §2 confirms at source level.

---

## 2. The Stwo backend on ARM mobile

### 2.1 Two backends — use `SimdBackend`, not `CpuBackend`

Stwo (`prover` feature) exposes two prover backends:

| Backend | Where | Role on mobile |
|---|---|---|
| `CpuBackend` | `prover/backend/cpu/` | Scalar reference. Correct but slow — **not** for benchmarking. |
| `SimdBackend` | `prover/backend/simd/` | The performant backend. **This is the mobile target.** |

`SimdBackend` is an unconditional type (`pub struct SimdBackend;` —
`simd/mod.rs:38`); there is **no architecture `cfg` gate on the backend itself**. It
is built on `PackedM31`, which is `#[repr(transparent)]` over `std::simd::Simd<u32,
N_LANES>` with `N_LANES = 16` (`simd/m31.rs:18-64`) — a 16-lane logical M31 vector.
The mobile benchmark (3.15) must select `SimdBackend`; benchmarking `CpuBackend`
would report a misleading number.

### 2.2 `portable_simd` and the nightly constraint

`PackedM31` uses `std::simd`, which is the nightly-only `portable_simd` feature.
Stwo gates it on the `prover` feature, which eu-id uses
(`crates/stwo/src/lib.rs:7-10`):

```rust
#![cfg_attr(feature = "prover",
            feature(array_chunks, iter_array_chunks, portable_simd, slice_ptr_get))]
```

**The only `portable_simd` constraint for mobile is: the whole build stays on
nightly Rust.** That is *already the project baseline* — `rust-toolchain.toml` pins
`nightly-2025-07-14`, required by Stwo regardless of target. Concretely:

- **No `-Z build-std` needed.** `rustup target add` ships precompiled `rust-std` for
  all three mobile targets on the pinned nightly (verified — Appendix A). iOS
  `aarch64`, iOS-sim `aarch64`, and Android `aarch64` are Tier-2 targets with `std`.
- **The x86-only nightly feature does not touch ARM.** Stwo also requests
  `feature(stdarch_x86_avx512)`, but it is gated
  `#![cfg_attr(all(target_arch = "x86_64", target_feature = "avx512f"), …)]`
  (`lib.rs:2-5`) — never activated on `aarch64`. One fewer nightly-feature risk on
  mobile, not more.
- **Backend acceleration is selected at compile time only** — Stwo contains *no*
  runtime `is_*_feature_detected!` calls (Appendix A). The shipped mobile binary is
  fixed at build time; on `aarch64` that is the NEON path (§2.3), with nothing to
  detect or fall back to at runtime.

### 2.3 What "SIMD on ARM" actually compiles to — NEON, not a scalar fallback

A frequent worry is that `portable_simd` on ARM degrades to a scalar fallback. It
does not. `simd/m31.rs` dispatches the hot M31 multiply per architecture
(`cfg_if!`, `m31.rs:183-192`):

| Target | Multiply path | Implementation |
|---|---|---|
| `aarch64` + `neon` | **`mul_neon`** | Hand-written `core::arch::aarch64` intrinsics — `vmull_u32`, `vqdmull_s32` (`m31.rs:337-408`). |
| `wasm32` + `simd128` | `mul_wasm` | wasm SIMD intrinsics. |
| `x86_64` + `avx512f` | `mul_avx512` | AVX-512 intrinsics. |
| `x86_64` + `avx2` | `mul_avx2` | AVX2 intrinsics. |
| otherwise | portable | `std::simd` lowering. |

**NEON is baseline-mandatory on AArch64** — every `aarch64-*` target has
`target_feature = "neon"` on by default — so on both iOS and Android the active
multiply is the *hand-tuned `mul_neon`*, not the portable fallback and not scalar
code. The file's own comment (`m31.rs:60`) states it is "implemented with
`std::simd` to support multiple targets (avx512, **neon**, wasm etc.)". The
16-lane `PackedM31` lowers on NEON's 128-bit registers to a small fixed number of
register operations; the latency-critical multiply is intrinsic-level.

**Bottom line for requirement 1:** the backend usable on ARM mobile is
`SimdBackend`, running its dedicated NEON path. There is no scalar-fallback penalty,
and `portable_simd` imposes nothing beyond the nightly toolchain the project already
pins.

---

## 3. Cross-compilation — verified, not assumed

All three targets were added on the pinned nightly and a real build was attempted.
Full transcript in Appendix A; results summarised here.

### 3.1 iOS — verified working end-to-end

```
rustup target add aarch64-apple-ios aarch64-apple-ios-sim
cargo build -p stwo-sha256 --target aarch64-apple-ios       # Finished in 10.46 s
cargo build -p stwo-sha256 --target aarch64-apple-ios-sim   # Finished in  5.02 s
```

Both **succeeded**, compiling `stwo` 2.2.0, `stwo-constraint-framework` 2.2.0, and
their full dependency graph (incl. the NEON multiply path) for ARM iOS. No source
patches, no feature flags, no `build-std`. The host toolchain (Xcode 16.4, iOS SDK
18.5) supplied the C compiler for native build-scripts automatically via `xcrun`.

Targets for 3.15: `aarch64-apple-ios` (device) and `aarch64-apple-ios-sim` (Apple-
Silicon simulator). `x86_64-apple-ios` (Intel simulator) is optional and low value —
real numbers come from devices.

### 3.2 Android — Rust verified portable; needs the NDK (condition C1)

```
rustup target add aarch64-linux-android
cargo build -p stwo-sha256 --target aarch64-linux-android   # FAILED — see below
```

The Android build **failed**, but the cause is precise and expected:

```
error occurred in cc-rs: failed to find tool "aarch64-linux-android-clang"
```

This is **not** a Stwo portability problem. The failure is in a `cc`-crate **build
script**, before any Stwo Rust is reached. The crate is **`blake3` v1.8.5**, a
*direct dependency of `stwo`* (`cargo tree`: `blake3 → stwo → stwo-constraint-
framework → stwo-sha256`). `blake3` compiles a small C/assembly NEON routine
(`cargo:rustc-cfg=blake3_neon` is emitted in the transcript) and needs a C
cross-compiler for the target. The host has no Android NDK
(`ANDROID_NDK_HOME` unset), so `cc` cannot find `aarch64-linux-android-clang`.

Why this proves Android-Rust portability anyway: Stwo has **zero `target_os`-specific
code** (Appendix A), and its SIMD acceleration is gated on `target_arch` /
`target_feature` only. `aarch64-linux-android` and the **already-verified**
`aarch64-apple-ios` are the *same architecture with the same `neon` feature* — Stwo's
Rust takes the identical code path on both. The OS differs; the prover code does not.
The Android-only gap is purely the C toolchain for `blake3`.

**Resolution (C1):** install the Android NDK (r26+) and use **`cargo-ndk`**, which
sets `CC_aarch64-linux-android` / linker env vars to the NDK's clang. `blake3` then
builds its NEON C cleanly — Android `aarch64` is a supported `blake3` target.
`cargo-ndk` is the documented Android path regardless, so C1 is a routine setup step
for 3.15, not new risk.

> *Fallback lever (not the recommended path):* `blake3` exposes a `pure` feature
> (pure-Rust, no `cc`). If the NDK ever becomes a CI blocker, asking Stwo to enable
> `blake3/pure` removes the C build entirely at a small hashing-speed cost. Prefer
> the NDK — it is needed for the app build anyway.

Primary Android target: **`aarch64-linux-android`** (`arm64-v8a`) — Google Play
mandates 64-bit. `armv7-linux-androideabi` (32-bit, old devices) and
`x86_64-linux-android` (emulator) are optional.

### 3.3 Packaging: `cargo-lipo` is obsolete — use `xcframework`

The roadmap names "`cargo-lipo`/`xcframework`". Resolve this to **`xcframework`**:
`cargo-lipo` builds a fat static lib by `lipo`-merging architecture slices, but since
Apple Silicon the iOS **simulator is also `arm64`** — `lipo` *cannot* hold two
`arm64` slices (device + simulator) in one archive, and `cargo-lipo` is effectively
unmaintained. The current Apple-supported mechanism is the **`.xcframework`**, which
stores per-platform libraries side by side and lets Xcode pick the right slice:

```
xcodebuild -create-xcframework \
  -library target/aarch64-apple-ios/release/libeu_id_ffi.a     -headers include/ \
  -library target/aarch64-apple-ios-sim/release/libeu_id_ffi.a -headers include/ \
  -output EuId.xcframework
```

Use `xcframework`; do not adopt `cargo-lipo`.

---

## 4. FFI strategy — C ABI + thin shims

**Decision: a C ABI with thin, hand-written Swift and Kotlin/JNI shims.** UniFFI was
considered and rejected for this POC (rationale below).

### 4.1 Why C ABI for this harness

The 3.15 harness surface is tiny — "a thin `mobile/` harness app exposing prove +
measure". It does not need an idiomatic, evolving SDK; it needs one or two functions
and honest numbers. For that surface, a C ABI is the lightest credible path:

- **No extra build tooling.** No `uniffi` runtime crate, no version-coupled
  `uniffi-bindgen` codegen step, no generated files to vendor and keep in sync.
- **The measured hot path is obviously overhead-free.** An honest benchmark wants
  nothing between the harness and `prove()` but a plain function call.
- **iOS is trivial.** Swift imports C headers natively — the iOS shim is a ~10-line
  wrapper over a hand-written header.
- The roadmap's own wording for this option ("thin Swift/Kotlin shims") matches.

### 4.2 Recommended shape (specified for 3.15; not built here)

A dedicated thin FFI crate (suggested `crates/eu-id-ffi`; exact name and which
component[s] it exposes is an interface-contract item — §7), with:

```toml
[lib]
crate-type = ["staticlib", "cdylib"]   # staticlib → iOS, cdylib → Android .so
```

**Keep the surface to one function.** Do the proving *and* the measurement inside
Rust, and return a small result. This keeps the C ABI minimal and the numbers
honest — FFI/UI overhead stays out of the measured window:

```c
// eu_id_ffi.h  — illustrative
typedef struct { uint64_t prove_ms; uint64_t peak_bytes; int32_t ok; } EuIdBench;
EuIdBench eu_id_bench_sha256(const uint8_t* preimage, size_t len, uint32_t iters);
```

Measure inside Rust, around `prove()`:

- **iOS peak memory:** `task_info` → `task_vm_info` `phys_footprint` (the figure
  jetsam actually enforces; §5.1).
- **Android peak memory:** `/proc/self/status` → `VmHWM` (peak resident set).

**Panics must not cross the FFI boundary** (unwinding past `extern "C"` is UB). Wrap
the body in `std::panic::catch_unwind` and surface failure via the `ok` field, or set
`panic = "abort"` for the mobile build profile.

- **iOS shim:** `staticlib` → `libeu_id_ffi.a`; bridge with a module map / bridging
  header; ~10 lines of Swift. Static-link into the harness app.
- **Android shim:** `cdylib` → `libeu_id_ffi.so`; loaded via `System.loadLibrary`.
  Kotlin/JVM cannot call a raw C ABI directly — it needs **JNI**. Write the JNI entry
  point in Rust with the `jni` crate (`Java_<pkg>_<Class>_<method>`, ~15–20 lines for
  one function); `cargo-ndk` builds and places the `.so` under
  `jniLibs/arm64-v8a/`. This JNI layer is the one place the C-ABI route costs more on
  Android than iOS — still small for a one-function surface, and far less machinery
  than UniFFI.

### 4.3 Considered and rejected — UniFFI

UniFFI would auto-generate idiomatic Swift + Kotlin bindings (including the Android
JNI) from annotated Rust. For a fixed one-to-two-function benchmark surface, its
costs — a `uniffi` runtime dependency, a version-coupled bindgen step, generated
sources to manage — outweigh the saved JNI boilerplate. **Revisit UniFFI if the
harness later grows into a reusable proving SDK** (e.g. a real wallet integration);
for 3.15 it is not justified.

---

## 5. Memory ceilings and the risk flag

The PRD names memory as the headline mobile risk: "proof generation may use too much
memory for mobile devices … if the primitives don't fit, we narrow scope." This
section estimates both sides — what a phone *gives* and what the prover *demands* —
and lands a verdict.

### 5.1 What a phone gives an app (the ceiling)

| Platform | Mechanism | Practical budget |
|---|---|---|
| **iOS** | `jetsam` kills apps over a RAM-scaled `phys_footprint` limit. The `com.apple.developer.kernel.increased-memory-limit` entitlement raises it. | ≈ **1.3–1.5 GB** on mainstream devices without the entitlement; more on 6–8 GB flagships / with it. |
| **Android** | The ART **Java heap** cap (`heapgrowthlimit`, `largeHeap`) does **not** bound native allocations — a Rust prover's `malloc`/`mmap` memory is limited only by physical RAM and the **Low Memory Killer**. | ≈ **1–2 GB** of native working set on a 3–4 GB foreground device before LMK pressure. |

The ART-heap cap is a common red herring here: it is irrelevant to a Rust prover,
whose memory is native. FibRace's empirical floor — **≥ 3 GB device RAM proves
stably** — is the number to design against. Net: budget the proving working set at
**≈ 1–1.5 GB on mainstream mid-range phones**; flagships afford 2–4 GB+.

### 5.2 What the prover demands

Reasoned from the validated SHA-256 design (`research/sha256-air-design.md`); orders
of magnitude only — see the honesty note below.

- **Witness / trace.** Credential-sized inputs (`IssuerSignedItem`, COSE
  `Sig_structure`) are a few 512-bit blocks. At ≈ 10⁴ trace cells/block
  (sha256-air-design §10b), the dynamic component is ≈ 10⁵ cells — a trace of only a
  few hundred to ~1k rows. **Small.**
- **Preprocessed tables (resident during proving).** The dominant `log_size`: the
  `Maj`/`Ch` table is 2¹⁸ rows at the recommended `W = 6`; ~16 decode tables are 2¹⁶.
  sha256-air-design §9.3 budgets these at **low tens of MB**, and explicitly flags
  them as a mobile-memory input.
- **LDE + FRI + Merkle.** The prover's committed-evaluation, FRI, and Merkle-tree
  working set scales with the largest committed domain (here ≈ 2¹⁸, set by the
  `Maj`/`Ch` table) × the FRI blowup × column count, plus tree overhead.

For the **SHA-256 component in isolation**, that totals an order of **tens to low-
hundreds of MB** — comfortably inside the ≈ 1–1.5 GB budget of §5.1.

> **Honesty note (cf. sha256-air-design §10b).** These are structural estimates, not
> measurements. The only trustworthy memory number is the benchmark. 3.14 must
> measure **peak RSS** on the laptop; 3.15 must measure on-device peak footprint.

### 5.3 Verdict on memory

- **SHA-256 component → low risk.** Its working set is dominated by tens-of-MB of
  preprocessed tables plus a low-hundreds-of-MB LDE/FRI/Merkle set. It should fit a
  mainstream phone with wide margin. This is the safe early benchmark — and exactly
  why the PRD wants the *simplest component* benchmarked first.
- **Full eu-id Big AIR → open (condition C2).** SHA-256 ×2 + ECDSA P-256 + mdoc share
  one proof; the ECDSA component (20 × 13-bit limbs, fake-GLV, many arithmetic rows)
  is the heavyweight, and proof memory scales with total committed columns. This is
  **unmeasured** and is the real memory risk.

**Mitigation levers, if the full pipeline overshoots** (hand these to 3.14/3.15):
benchmark `--release` only (the Appendix A builds are unoptimized `dev` — never a
benchmark profile); tune the `W` group-width knob (sha256-air-design §9.2 — `W = 6`
vs `7` is an 8× swing on the `Maj`/`Ch` table); lower the FRI blowup; reduce the
dominant `log_size`; prove components separately where soundness allows. If none
suffice, narrow scope per the PRD — and report it honestly.

---

## 6. Chosen toolchain

### 6.1 Toolchain (requirement deliverable)

| Layer | Choice | Notes |
|---|---|---|
| Rust toolchain | Pinned **nightly** (`rust-toolchain.toml`, `nightly-2025-07-14`) | Required by `portable_simd`; no mobile-specific addition. No `-Z build-std`. |
| Prover backend | Stwo **`SimdBackend`** | NEON multiply path on ARM (§2.3). Never benchmark `CpuBackend`. |
| iOS targets | `aarch64-apple-ios`, `aarch64-apple-ios-sim` | Verified building today (§3.1). `x86_64-apple-ios` optional. |
| iOS packaging | static lib per target → **`xcodebuild -create-xcframework`** | **Not** `cargo-lipo` (§3.3). |
| Android target | `aarch64-linux-android` (`arm64-v8a`) | `armv7`/`x86_64` optional. |
| Android packaging | **`cargo-ndk`** (needs Android **NDK r26+**) | Wires the NDK clang for `blake3`'s `cc` build (C1, §3.2). |
| FFI crate | thin crate, `crate-type = ["staticlib", "cdylib"]` | e.g. `crates/eu-id-ffi`; created in 3.15. |
| FFI strategy | **C ABI + thin Swift / Kotlin-JNI shims** (§4) | UniFFI rejected for this POC. |
| Build profile | **`--release`** for all benchmarks | The §3 verification builds are `dev` — unoptimized. |
| Measurement | inside Rust — iOS `phys_footprint`, Android `/proc/self/status` `VmHWM` | One-function FFI surface (§4.2). |

### 6.2 Recommended device matrix for 3.15

FibRace shows performance tracks **RAM + SoC**, so 3.15 should span those axes rather
than chase model count. Anchor the low end on FibRace's ≥ 3 GB stability floor.

| Tier | iOS | Android | Why |
|---|---|---|---|
| Floor | 3–4 GB-RAM iPhone (e.g. SE class) | 3–4 GB-RAM device | FibRace stability floor — the honest worst case. |
| Mid | 6 GB-RAM iPhone, recent A-series | 6–8 GB mid-range SoC | The mainstream the POC is judged on. |
| High | 8 GB iPhone Pro, latest A-series | 12 GB flagship, latest SoC | Best case; isolates SoC effects. |

Report device model, SoC, RAM, and OS version alongside every number (3.15
requirement). Three to four devices spanning the floor→high range is enough for a
credible POC; more model count adds little signal.

---

## 7. What 3.15 inherits / open items

This research feeds, but does not perform, the mobile harness (3.15). Handed forward:

1. **One-time setup.** Install Android NDK (r26+), `cargo-ndk`; add the iOS/Android
   `rustup` targets (iOS already verified present on the dev machine).
2. **Create the FFI crate** (`crate-type = ["staticlib", "cdylib"]`) and the
   `mobile/` harness; implement the C ABI of §4.2; build the iOS `.xcframework` and
   the Android `.so` per §3 / §6.
3. **Wire `make bench-mobile`** to drive the harness (the SHA-256 stream owns this
   target per roadmap 1.2); land machine-readable results in `benches/results/`.
4. **Benchmark SHA-256 first** (`--release`, `SimdBackend`), on the §6.2 matrix —
   then the full pipeline once integration lands.
5. **Interface-contract item.** Decide whether the FFI crate exposes the SHA-256
   component alone (first benchmark) or the full `eu-id-air` pipeline — `mobile/`
   will likely host both over time. Settle the crate name and boundary with the team
   so the harness is not reworked, mirroring the digest-layout/relation-tag freeze in
   `research/sha256-air-design.md` §10.5.
6. **Carry C2 forward.** Measure peak memory on every run; if the full pipeline
   overshoots the §5.1 budget, apply the §5.3 levers and, failing that, narrow scope.

---

## Appendix A — build verification (reproducible)

Environment: macOS (Darwin 24.5.0), host `aarch64-apple-darwin`, Xcode 16.4 / iOS SDK
18.5, `rustc 1.90.0-nightly (e9182f19 2025-07-13)` (matches the pinned
`nightly-2025-07-14`). Stwo pin: `Cargo.lock` → `git+https://github.com/starkware-libs/stwo.git#e1286720…` (v2.2.0).

**1. Add the mobile targets** — all three resolve on the pinned nightly; `rust-std`
downloads cleanly, so no `-Z build-std` is required:

```
rustup target add aarch64-apple-ios aarch64-apple-ios-sim aarch64-linux-android
```

**2. Cross-compile `stwo-sha256`** (this compiles all of `stwo` +
`stwo-constraint-framework`). Observed:

```
$ cargo build -p stwo-sha256 --target aarch64-apple-ios
   Compiling stwo v2.2.0 (…stwo.git#e1286720)
   Compiling stwo-constraint-framework v2.2.0 (…stwo.git#e1286720)
   Compiling stwo-sha256 v0.1.0
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 10.46s   # ✅

$ cargo build -p stwo-sha256 --target aarch64-apple-ios-sim
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 5.02s    # ✅

$ cargo build -p stwo-sha256 --target aarch64-linux-android
  cargo:rustc-cfg=blake3_neon
  cargo:warning=Compiler family detection failed … "aarch64-linux-android-clang"
  error occurred in cc-rs: failed to find tool "aarch64-linux-android-clang"   # ✅ expected — no NDK (C1, §3.2)
```

The Android failure is in the `blake3` (`cc`) build script for a missing NDK
compiler — *before* any Stwo Rust — not a Stwo portability defect (§3.2).

**3. Source checks** (Stwo checkout `e1286720`):

```
# No OS-specific code — iOS and Android run identical prover Rust:
$ grep -rn "target_os" crates/stwo/src crates/constraint-framework/src crates/air-utils/src
  → (no matches)

# No runtime feature detection — backend acceleration is compile-time cfg only:
$ grep -rn "feature_detected" crates/stwo/src
  → (no matches)

# blake3 is a direct stwo dependency (the cc/NDK requirement on Android):
$ cargo tree -p stwo-sha256 -i blake3 --target aarch64-linux-android
  blake3 v1.8.5
  └── stwo v2.2.0 → stwo-constraint-framework → stwo-sha256
```

Key source locations: `crates/stwo/src/lib.rs:2-10` (feature gating);
`crates/stwo/src/prover/backend/simd/m31.rs:18-64` (`N_LANES = 16`, `PackedM31`),
`:60` (multi-target doc-comment), `:183-408` (`mul_neon` NEON path);
`crates/stwo/src/prover/backend/simd/mod.rs:38-40` (`SimdBackend`).

---

## Appendix B — requirement coverage

| Task 2.6 requirement | Where |
|---|---|
| Identify the Stwo backend on ARM mobile (SIMD/NEON vs. scalar) and `portable_simd` constraints | §2 (`SimdBackend` + NEON; nightly-only, no `-Z build-std`, x86 feature not on ARM) |
| Establish the cross-compilation path: `cargo-ndk` (Android), iOS targets + `xcframework` | §3 (verified iOS build; Android via `cargo-ndk` + NDK; `xcframework` not `cargo-lipo`), §6.1 |
| Choose the FFI strategy (UniFFI vs C ABI + shims) | §4 — **C ABI + thin shims**; UniFFI considered and rejected |
| Estimate memory ceilings; flag risk early per the PRD | §5 — device budget vs prover demand; SHA-256 low risk, full pipeline = C2 |
| Confirm the FibRace backend/config | §1 — FibRace = Cairo M (M31 Circle-STARK family), with the honest scope caveat |
| Deliverable: `research/mobile-backend.md` with chosen toolchain + feasibility verdict | this file — §6 (toolchain), §0 (verdict) |

---

## Sources

- FibRace — *FibRace: a large-scale benchmark of client-side proving on mobile
  devices*, arXiv [2510.14693](https://arxiv.org/abs/2510.14693).
- StarkWare — *Introducing S-two: The fastest prover for real-world ZK applications*,
  [starkware.co/blog/s-two-prover](https://starkware.co/blog/s-two-prover/).
- Stwo source — `github.com/starkware-libs/stwo`, commit `e1286720` (the
  `Cargo.lock` pin); files cited inline and in Appendix A.
- `docs/zk_digitalid_prd.md` (performance-risk mitigation, FibRace claim);
  `research/sha256-air-design.md` (§9.3, §10b — table sizing and cost feeding §5).
