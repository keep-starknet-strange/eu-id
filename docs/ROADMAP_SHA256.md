# eu-id — SHA-256 Stream Roadmap

> Personal workstream roadmap for the **SHA-256 component** (`crates/stwo-sha256`).
> This is a filtered slice of the master `docs/ROADMAP.md` — item IDs are kept
> **identical to the master** so the team can cross-reference (`/do-task` still
> targets `docs/ROADMAP.md`). Items owned by the other two streams are not
> reproduced here; see "Not in this stream" at the bottom.

---

## Team Split

The eu-id pipeline is three near-independent component crates joined by an integration crate:

| Stream | Crate | Owner |
|---|---|---|
| **B — SHA-256 AIR** | `stwo-sha256` | **this roadmap** |
| A — ECDSA P-256 AIR | `stwo-p256` | teammate |
| C — Credential & age gadget | `stwo-mdoc` | teammate |
| Integration | `eu-id-air` | shared, done last |

## Your Ownership & Boundaries

**You own:** the `stwo-sha256` crate and items **2.5, 2.6, 3.9, 3.14, 3.15**. You are also the natural owner of the early post-week-2 go/no-go benchmark, since the PRD says to benchmark the *simplest component* first — that is SHA-256.

**You create only your own crate.** Phase 1 is split per stream so nobody scaffolds another team's crate. Your 1.1 below creates **only** `crates/stwo-sha256` — `stwo-mdoc` and `eu-id-air` are created by their owners in their own Phase 1. The remaining setup (Makefile, Docker, CI, lint) is shared scaffold, done once by the team.

**Upstream you depend on (consume, don't build):**
- **3.1 — shared range-check / limb / LogUp foundation** (ECDSA stream). All three crates need range checks and M31 limb arithmetic. Agree the convention before you build, or you'll rework it.
- **2.4 — mdoc / COSE structure analysis** (credential stream). This deliverable tells you exactly which byte structures you hash (the `IssuerSignedItem` and the COSE `Sig_structure`), including padding and length.

**Downstream that depends on you (keep your interface stable):**
- **3.10** (credential stream) consumes your `IssuerSignedItem` digest for the `valueDigests` membership check.
- **3.13** (integration) binds your `Sig_structure` digest to the ECDSA `z` input via LogUp.

The single most important thing for not stepping on toes: **freeze your digest-output column layout and LogUp relation tags early** and write them down (see the Interface Contract at the bottom).

---

## Phase 1: Project Setup

Phase 1 is **split per stream** so no one scaffolds another team's crate. Master `docs/ROADMAP.md` item 1.1 creates all crates at once; here it is scoped down — you create **only** `crates/stwo-sha256`. The `stwo-mdoc` and `eu-id-air` crates are created by their owners in their own Phase 1.

### 1.1 Create the `stwo-sha256` Crate

**Description**: Create your own component crate and register it in the workspace, without touching the other teams' crates. This is the SHA-256-scoped slice of master item 1.1.

**Requirements**:
- [ ] `cargo new --lib crates/stwo-sha256`
- [ ] Add `stwo` and `stwo-constraint-framework` dependencies (git, `prover` feature — match `crates/stwo-p256/Cargo.toml`)
- [ ] Append `"crates/stwo-sha256"` to the root `Cargo.toml` `[workspace] members` list — and nothing else
- [ ] Create the `research/` and `benches/` folders when you first need them for items 2.5/2.6 and 3.14/3.15
- [ ] Do **not** create `crates/stwo-mdoc`, `crates/eu-id-air`, or `bin/` — those belong to their owners

**Implementation Notes**: The root `Cargo.toml` `members` array is the one file all three streams edit — only ever *append your own* line, and only once the crate directory exists (Cargo errors on a listed-but-missing member). A workspace builds fine with a subset of the planned crates present, so the other crates not existing yet does not block you. Use edition 2021 to match `stwo-p256`.

### Shared scaffold (team — done once, not crate creation)

These touch the whole workspace, are done once by whoever picks them up, and must not assume all three crates exist. Full detail in `docs/ROADMAP.md` items 1.2–1.5.

- **1.2 Makefile & Build Tooling** — *your stake:* the `make bench` / `make bench-mobile` targets (you own benchmarking).
- **1.3 Docker & docker-compose** — shared, no SHA-256-specific slice.
- **1.4 CI Pipeline** — shared; `cargo test --workspace` picks up `stwo-sha256` automatically once it is a member.
- **1.5 Linting, Formatting & Pre-commit Hooks** — shared, no SHA-256-specific slice.

---

## Phase 2: Research — SHA-256 owned

Each task produces a markdown deliverable in `./research/`.

### 2.5 SHA-256 M31 AIR Design Validation

**Description**: Validate (do not assume) the bit-index-partitioned lookup-table SHA-256 design in `docs/sha256_air_design.md` before building the AIR — the reference `../sha256-air` design has been flagged as possibly wrong.

**Requirements**:
- [ ] Verify the L0/L1/L2 + H0/H1/H2 bit-partition and the lookup-table decomposition of `Σ`, `ch`, `maj` against the SHA-256 spec
- [ ] Confirm the claimed cell costs and the output-bit-set derivation (`{(a·11+b·20) mod 32}`)
- [ ] Independently audit the `../sha256-air` reference crate for correctness rather than copying it
- [ ] Settle the lookup-table sizes and the M31 representation (16-bit low / high split)
- [ ] Deliverable: `research/sha256-air-design.md` — a validated, corrected design ready to implement

**Implementation Notes**: Treat `../sha256-air` and `../cosine-similarity-air` as learning references only. The decomposition trick (partition input bits so each output bit depends on a small index set, then table-lookup) is sound in principle; the risk is in the specific index sets and costs. Multi-block hashing (the credential exceeds one 512-bit block) must be in the validated design.

### 2.6 Stwo Mobile Backend Feasibility

**Description**: Determine how Stwo proof generation runs on iOS and Android, since mobile benchmarking is an MVP requirement, not an afterthought.

**Requirements**:
- [ ] Identify the Stwo backend usable on ARM mobile (SIMD/NEON vs. scalar fallback) and any `portable_simd` constraints
- [ ] Establish the cross-compilation path: `cargo-ndk` for Android, iOS targets + `cargo-lipo`/`xcframework`
- [ ] Choose the FFI strategy (UniFFI, C ABI + thin Swift/Kotlin shims)
- [ ] Estimate memory ceilings — proof generation memory must fit a phone; flag risk early per the PRD
- [ ] Deliverable: `research/mobile-backend.md` with the chosen toolchain and a feasibility verdict

**Implementation Notes**: The PRD cites FibRace (Oct 2025) generating STARK proofs on 1,400 phone models in under 5s — confirm what backend/config that used. The PRD mandates an early benchmark of the simplest component (after week 2) before sinking effort into the full system; this research feeds that go/no-go.

---

## Phase 3: Build — SHA-256 owned

### 3.9 SHA-256 Compression & Multi-Block Hashing AIR

**Description**: The `stwo-sha256` crate — a SHA-256 AIR over M31 implementing compression, message scheduling, and multi-block hashing, per the validated 2.5 design.

**Requirements**:
- [ ] Bit-index-partitioned lookup tables for `Σ0`/`Σ1`/`σ0`/`σ1`, `ch`, `maj` (16-bit low/high M31 split)
- [ ] Round function and 64-round message schedule constraints
- [ ] Multi-block chaining (initial vector → block → updated state) for credential-sized inputs
- [ ] Padding constraints (length encoding, `0x80` marker)
- [ ] Native SHA-256 witness generator; property tests against the `sha2` crate including multi-block vectors
- [ ] Standalone prover/verifier for the SHA-256 component

**Implementation Notes**: Implement the *validated/corrected* design from `research/sha256-air-design.md` (2.5), not `docs/sha256_air_design.md` verbatim and not the `../sha256-air` reference verbatim. Used twice in the pipeline (`IssuerSignedItem` hash, COSE `Sig_structure` hash) — the digest-output columns must be cleanly exposable for the LogUp binding done by the integration stream (3.13). Builds on the shared lookup/limb foundation from 3.1 (coordinate with the ECDSA stream).

### 3.14 Laptop Benchmark Suite — SHA-256 slice + shared harness

**Description**: Criterion benchmarks producing the honest performance numbers the POC's argument rests on, on laptop hardware. You own the benchmark *harness/infrastructure* and the SHA-256 component numbers; the ECDSA and mdoc owners contribute their component numbers, and the full-pipeline run happens post-integration.

**Requirements**:
- [ ] Build the criterion harness in `benches/`: measure proof-generation time, proof size, peak memory, verification time
- [ ] SHA-256 component benchmark, wired as soon as 3.9 lands
- [ ] Run the SHA-256 benchmark as the **post-week-2 go/no-go gate** (PRD performance-risk mitigation)
- [ ] Machine-readable results checked into `benches/results/`
- [ ] *(cross-cutting)* slots for the ECDSA/mdoc per-component breakdown + full-pipeline run — others/integration plug in

**Implementation Notes**: The PRD's performance-risk mitigation is *benchmark early* — wire the SHA-256 benchmark before the full system exists. If the primitives don't fit, that's a scope signal: narrow scope rather than ship a misleading result. Keep the harness component-agnostic so the other streams drop in without reworking it.

### 3.15 Mobile Benchmark Harness (iOS/Android)

**Description**: Cross-compile the prover for mobile and benchmark proof generation on real iOS and Android hardware — an MVP deliverable.

**Requirements**:
- [ ] Cross-compilation per 2.6: `cargo-ndk` (Android), iOS targets + `xcframework`
- [ ] FFI bindings and a thin `mobile/` harness app exposing prove + measure
- [ ] On-device measurement of proof-gen time and peak memory across a few representative devices
- [ ] `make bench-mobile` driving the harness; results in `benches/results/`

**Implementation Notes**: The PRD targets the FibRace bar — sub-5s STARK proofs on consumer phones. Memory ceiling is the headline risk: if proof generation exhausts phone RAM, that is a scope signal. Report device models and OS versions honestly alongside the numbers. The harness benchmarks the SHA-256 component first, then the full pipeline once integration lands.

---

## Interface Contract — the "don't step on toes" boundary

Freeze and document these early (a short note in `docs/` or the crate README) so the other streams develop against a stable contract:

1. **Digest output column layout.** How the 256-bit SHA-256 digest is exposed as M31 columns (limb count, bit width, low/high split). The mdoc stream (3.10) and integration (3.13) both read this.
2. **LogUp relation tag names.** Agree the relation tags for digest↔`valueDigests` membership and `Sig_structure` digest↔ECDSA `z` with the other two owners up front. Mismatched tags = silent imbalance.
3. **Multi-block input convention.** How preimage bytes are fed and padded — the mdoc stream produces the `IssuerSignedItem`/`Sig_structure` bytes you hash (defined by research 2.4).
4. **Shared foundation (3.1).** Use the ECDSA stream's range-check / limb / LogUp helpers; don't fork your own. Settle this before writing constraint code.

## Not in this stream (for reference)

Owned by teammates — do **not** implement these:

- **3.1–3.8** — ECDSA P-256 AIR (Stream A). 3.1 is your *upstream dependency*, not your task.
- **3.10–3.11** — mdoc parsing, `valueDigests` membership, age-over-18 gadget (Stream C). 2.4 is your *upstream dependency*.
- **3.12 (native end-to-end witness generator), 3.13 (integration Big AIR), 3.16 (writeup & Topic G submission)** — cross-cutting / integration. Your contribution to these is the SHA-256 native witness generator (delivered in 3.9) and the benchmark numbers (3.14/3.15).
- **Phase 4 / Phase 5** — post-MVP; see `docs/ROADMAP.md`.
