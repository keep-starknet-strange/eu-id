# eu-id Development Roadmap

---

This roadmap covers the eu-id STARK proof-of-concept: an in-circuit pipeline that proves *"holder is over 18"* from an ISO mdoc credential without disclosing the date of birth.

**Already complete (omitted from the roadmap):** the Cargo workspace and the `stwo-p256` crate exist; the crate's native reference layer is implemented and tested — `types.rs` (`U256`, P-256 constants), `limbs.rs` (`LimbsM31`, schoolbook multiplication, carry propagation), `field_ops.rs` (`mul_mod`/`add_mod`/`sub_mod` witness generators), `curve.rs` (native point arithmetic, `mod_inverse`), and `ecdsa.rs` (textbook ECDSA verification validated against the `p256` crate). The frozen v8 AIR spec (`crates/stwo-p256/docs/p256_fake_glv_air_full_spec.md`) and PRD (`docs/zk_digitalid_prd.md`) also exist.

**The build target** is everything else: the ECDSA AIR (`trace.rs`/`constraints.rs`/`stark.rs` are `todo!()` stubs), the SHA-256 and mdoc crates, the integration Big AIR, benchmarks, and the Topic G submission.

---

## Phase 1: Project Setup

### 1.1 Workspace Crate Structure

**Description**: Extend the existing single-crate workspace into the multi-crate monorepo the full pipeline needs, so SHA-256, mdoc parsing, and integration each have a home before feature work begins.

**Requirements**:
- [ ] Add `crates/stwo-sha256`, `crates/stwo-mdoc`, and `crates/eu-id-air` crates with `cargo new --lib`
- [ ] Register all crates as workspace members in the root `Cargo.toml`
- [ ] Create `bin/` for the demo CLI, `benches/` for criterion benchmarks, `scripts/` for bash helpers, and `research/` for Phase 2 deliverables
- [ ] Wire inter-crate dependencies (`eu-id-air` depends on the three component crates; each component depends on `stwo` + `stwo-constraint-framework`)
- [ ] Shared dev-dependency set (`p256`, `ecdsa`, `sha2`, `rand`, `hex`) hoisted via `[workspace.dependencies]`

**Implementation Notes**: Keep `rust-toolchain.toml` pinned to the existing `nightly-2025-07-14`. Mirror the `../falcon-air` layout (`crates/<component>` + root `bin/`). New crates may use edition 2021 to match `stwo-p256`; align editions across the workspace. Do not break the existing `stwo-p256` crate — only add to the workspace.

### 1.2 Makefile & Build Tooling

**Description**: A top-level Makefile exposing every common operation so contributors and CI share one interface.

**Requirements**:
- [ ] `make dev` (watch + check), `make run` (demo prover), `make test`, `make check` (clippy + fmt, CI-equivalent)
- [ ] `make bench` (laptop criterion suite) and `make bench-mobile` (mobile harness)
- [ ] `make prove` / `make verify` targets driving the CLI against a sample credential
- [ ] `.PHONY` declarations; targets degrade gracefully when optional tools (`cargo-watch`) are absent

**Implementation Notes**: Use `../sha256-air/Makefile` as the baseline pattern. Keep `make check` exactly equal to the CI lint step (`cargo clippy -- -D warnings && cargo fmt -- --check`) so local and CI results never diverge.

### 1.3 Docker & docker-compose

**Description**: A reproducible containerised build/test environment that pins the nightly toolchain, insulating the project from host Rust drift.

**Requirements**:
- [ ] `Dockerfile` based on a Rust nightly image, installing the pinned toolchain and `rustfmt`/`clippy`
- [ ] `docker-compose.yml` services for building, running the test suite, and generating a proof
- [ ] Build cache layer for the `stwo` git dependency to keep rebuilds fast
- [ ] `make` targets delegate to compose where containerisation helps

**Implementation Notes**: Stwo's SIMD backend prefers x86-64 AVX2; document this in the image and note non-AVX2 fallback. Mobile cross-compilation toolchains (`cargo-ndk`, iOS targets) are out of scope here — handled in 3.16.

### 1.4 CI Pipeline

**Description**: GitHub Actions running build, test, and lint on every push so regressions in a multi-component cryptographic codebase are caught immediately.

**Requirements**:
- [ ] Workflow installing the pinned nightly and caching cargo registry + `stwo` build artifacts
- [ ] Jobs: `cargo build`, `cargo test --workspace`, `cargo clippy -- -D warnings`, `cargo fmt -- --check`
- [ ] Fail the build on warnings; surface test output on failure
- [ ] (Optional) a longer scheduled job running the full proof-generation end-to-end test

**Implementation Notes**: Proof generation is slow — keep it out of the per-push path or behind a scheduled trigger. Cache the `stwo` git dependency aggressively; it dominates cold build time.

### 1.5 Linting, Formatting & Pre-commit Hooks

**Description**: Enforce consistent style and catch lint errors before commit, reducing review noise across the workspace.

**Requirements**:
- [ ] `rustfmt.toml` and a workspace `clippy` lint configuration
- [ ] Pre-commit hook (script or `pre-commit` framework) running `cargo fmt` and `cargo clippy`
- [ ] `scripts/check.sh` reproducing the CI lint step locally
- [ ] Document the contributor workflow in a top-level `README.md`

**Implementation Notes**: Keep hooks fast — fmt + clippy only, never the full test suite. The README should also state the research-prototype / "not audited" disclaimer up front, as `../falcon-air/README.md` does.

---

## Phase 2: Research

Each task produces a markdown deliverable in `./research/`. These resolve the open technical risks before implementation commits to a design.

### 2.1 M31 Headroom Audit (BLOCKER)

**Description**: Discharge the headroom blocker called out in the v8 spec: prove that every big-integer constraint equation cannot alias to zero in M31 while being nonzero as an integer. Until this is done, no arithmetic row type is sound.

**Requirements**:
- [ ] For each equation type — FnMul (256×256), Fp Solinas mul, RCB Algorithm 6 (DOUBLE), RCB Algorithm 5 (ADD), AFFINE_EXPORT, certificate equivalence, FINAL_CHECK, fake-GLV scalar (256×128) — compute `max |combined_coeff[i]|`
- [ ] Verify each against the `(2³¹ − 2)/2 = 2³⁰ − 1` bound; fill the headroom table from the v8 spec
- [ ] For any equation that fails, specify the split (intermediate witness columns or widened carry range)
- [ ] Deliverable: `research/m31-headroom-audit.md` with a machine-checked table and a small verification script

**Implementation Notes**: Carry equations have the form `prod_coeff[i] − qn_coeff[i] − result_limb[i] + carry[i] − 2¹³·carry[i+1]`. The RCB complete formulas have large intermediate expressions and the Solinas reduction introduces signed coefficients from misaligned exponents (96/192/224 are not multiples of 13) — these are the likely failure points. A short Rust or Python script that bounds each coefficient symbolically makes the audit reproducible.

### 2.2 RCB Complete-Formula Verification

**Description**: Verify the Renes–Costello–Batina exception-free formulas behave correctly on every degenerate input before they are encoded as constraints.

**Requirements**:
- [ ] Confirm RCB Algorithm 6 applied to projective infinity `(0,1,0)` yields a valid projective infinity (`Z_out = 0`, `Y_out ≠ 0`), not the forbidden `(0,0,0)`
- [ ] Confirm Algorithm 5 (complete mixed addition) is correct for `O+P`, `P+O`, `P+P`, `P+(−P)`, and generic `P+Q`
- [ ] Decide whether `DOUBLE(O)` needs an explicit conditional or can rely on Algorithm 6
- [ ] Add a native projective EC reference to `stwo-p256` and exercise it against the existing affine reference
- [ ] Deliverable: `research/rcb-formula-verification.md` with concrete substitutions and the conditional decision

**Implementation Notes**: The current `curve.rs` uses incomplete affine formulas (`λ = (y₂−y₁)/(x₂−x₁)`) — fine as a generic oracle but it cannot witness the projective chain. A homogeneous-projective reference is needed for trace generation regardless; build it here. The fake-GLV table intentionally hits `P+(−P)=O` (e.g. `S=1`), so completeness is not optional.

### 2.3 Fake-GLV Hint Generation

**Description**: Implement and validate the lattice-reduction algorithm that produces fake-GLV hints (`s1`, `s2_abs`, `s2_sign_bit`) for a given scalar, since the AIR *verifies* a certificate but does not compute it.

**Requirements**:
- [ ] Implement the half-GCD / lattice reduction that decomposes a scalar `S` into `(s1, s2_signed)` with `s1 + S·s2_signed ≡ 0 mod n` and both components `< 2¹²⁸`
- [ ] Handle the zero-scalar branch (`S = 0`)
- [ ] Cross-check generated hints against Garaga-produced hints on a corpus of scalars
- [ ] Verify the v8 edge cases (`S = 1, n−1, 3, n−3, 3⁻¹, −3⁻¹`) produce valid certificates
- [ ] Deliverable: `research/fake-glv-hints.md` plus a hint generator usable by the trace builder

**Implementation Notes**: The decomposition is the cryptographic core that makes fake-GLV cheaper than a full 256-bit chain. Reference the Garaga implementation and the "Fake GLV" ethresear.ch writeup. The generator belongs in `stwo-p256` (native side) and feeds the trace generator implemented in 3.13.

### 2.4 ISO mdoc / COSE_Sign1 Structure Analysis

**Description**: Pin down exactly which bytes are hashed and signed in an ISO/IEC 18013-5 mdoc, so the SHA-256 and parsing gadgets target the right structures.

**Requirements**:
- [ ] Document the `MobileSecurityObject` CBOR layout: `valueDigests`, `docType`, `validityInfo`, `deviceKeyInfo`
- [ ] Document the `IssuerSignedItem` layout (`digestID`, `random`, `elementIdentifier`, `elementValue`) and how its digest enters `valueDigests`
- [ ] Document the COSE `Sig_structure` that ES256 actually signs (what `z` is the digest *of*)
- [ ] Decide the age strategy: extract `birth_date` and compute age, vs. verify the `age_over_18` boolean data element — and how the gadget handles both
- [ ] Produce a real or realistic sample mdoc credential + issuer key as a test vector
- [ ] Deliverable: `research/mdoc-structure.md` plus `scripts/` credential-generation tooling

**Implementation Notes**: mdoc data elements include purpose-built `age_over_NN` booleans, but the PRD explicitly frames the demo as DOB-based age computation — design the gadget around `birth_date` (CBOR `full-date`/`tdate`) and treat `age_over_18` as a simpler alternate path. This deliverable defines the byte layouts that 3.9–3.11 constrain.

### 2.5 SHA-256 M31 AIR Design Validation

**Description**: Validate (do not assume) the bit-index-partitioned lookup-table SHA-256 design in `docs/sha256_air_design.md` before building the AIR — the user has flagged that the reference `../sha256-air` design may be wrong.

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

## Phase 3: MVP

The core build. The ECDSA component follows the frozen v8 spec's 20-step implementation order; the items below group those steps. All in-circuit arithmetic is gated on the 2.1 headroom audit.

### ECDSA P-256 Verification AIR

### 3.1 Range-Check Lookup Infrastructure & Canonical Comparisons

**Description**: The lookup-table foundation every other ECDSA row depends on: range checks and canonical `< n` / `< p` comparisons.

**Requirements**:
- [ ] `Range13`, `Range9`, `Range11`, `Range128` preprocessed lookup tables with witness multiplicity columns
- [ ] `Selector4x4`, `Selector16Decode`, `FinalSelector` preprocessed selector tables
- [ ] Canonical comparison gadgets (`< n`, `< p`) via borrow witnesses
- [ ] Boolean constraint helper (`b·(1−b)=0`); `SignedCarryRange` table sized per carry analysis
- [ ] LogUp relations for every table; `Range13` fractions paired via `finalize_logup_in_pairs`

**Implementation Notes**: Steps 1 of the v8 implementation order. Static-table values are preprocessed and circuit-fixed; multiplicity columns are witness data. Reference `../falcon-air/crates/falcon/src/zq/range_check.rs` for the Stwo range-check pattern. Numerator degree must stay at 1 so paired LogUp degree stays ≤ 2.

### 3.2 Scalar-Field Multiplication (FnMul) & Digest Reduction

**Description**: The `SCALAR_SETUP` rows proving `s·u1 = z_red mod n` and `s·u2 = r mod n`, plus reduction of the message digest `z` modulo `n`.

**Requirements**:
- [ ] `FnMulEval` — full 256×256 generic-quotient multiplication, `A·B − Q·n − C = 0` with carry propagation
- [ ] Quotient bounded `Q < n` via borrow witness; operands bounded `< n`
- [ ] Digest reduction `z − z_red − z_ge_n·n = 0` with `z_ge_n ∈ {0,1}` and canonical `z_red`
- [ ] `z` top-limb 256-bit check (`z_limb[19] < 2⁹` via `Range9`)
- [ ] Trace generator + negative tests (`s·u1 ≠ z_red`, mutated `z_red`, `Q = n`)

**Implementation Notes**: Steps 2 of the v8 order. Replace the placeholder `MulModEval` in `constraints.rs`. The native `mul_mod_witness` in `field_ops.rs` provides the witness values directly. Generic quotient is acceptable here — scalar-field mul is not the bottleneck.

### 3.3 Base-Field Solinas Arithmetic

**Description**: P-256 base-field (`Fp`) multiplication and reduction using the Solinas identity, the hot path under all EC arithmetic.

**Requirements**:
- [ ] `FpSolinasEval` using `2²⁵⁶ = 2²²⁴ − 2¹⁹² − 2⁹⁶ + 1 mod p`
- [ ] Precomputed signed reduction matrix `coeff[k][j]` for misaligned high-limb positions
- [ ] Reduction equation `raw − solinas_fold(high) − result − correction·p = 0` with canonical result and signed carries
- [ ] Exact `correction` bound computed per operation type (mul/add/sub)
- [ ] All equations cross-checked against the 2.1 headroom table

**Implementation Notes**: Step 3 of the v8 order. Solinas exponents 96/192/224 are not multiples of `LIMB_BITS=13`, so the fold is a signed reduction matrix, not a limb permutation. This is the dominant cost — get it right and bounded before EC formulas build on it.

### 3.4 RCB Complete EC Operations & Affine Export

**Description**: The exception-free elliptic-curve doubling, complete mixed addition, and projective-to-affine export — all in homogeneous-projective coordinates.

**Requirements**:
- [ ] `EC_DOUBLE` via RCB Algorithm 6; `EC_ADD` via RCB Algorithm 5 with the `Uinf` operand-infinity conditional
- [ ] `STATE_LOAD` (affine→projective lift, `(0,1,0)` for infinity) and canonical point negation (`p − y` with `inf` gating)
- [ ] `AFFINE_EXPORT` with `state_is_inf` witness — `inf=0` proves `Z≠0`, `inf=1` proves `Z=0 ∧ X=0 ∧ Y≠0`
- [ ] `ON_CURVE` and `CERT_BIND` row types
- [ ] Completeness tests for `O+P`, `P+O`, `P+P`, `P+(−P)`, `DOUBLE(O)`, and `(0,0,0)` rejection

**Implementation Notes**: Steps 4–7 of the v8 order; depends on the 2.2 formula verification. No `inf_out` flag — internal state is pure homogeneous projective; infinity is detected only at boundary rows. `(0,0,0)` is forbidden as a projective point and must be rejected everywhere.

### 3.5 Fake-GLV Certificate: Scalar Equation & Selector Decomposition

**Description**: The `FAKE_GLV_SCALAR` row (256×128 signed small-multiplication) and the `SELECTOR_RECON` rows that reconstruct `s1`/`s2_abs` from 2-bit selector chunks.

**Requirements**:
- [ ] Scalar equation `S·s2_abs + (1−2·s2_sign_bit)·s1 − q·n = 0`
- [ ] Quotient bounds: `q[0..8] < 2¹³`, `q[9] < 2¹¹` (`Range11`), `q[10..19] = 0`
- [ ] `s1 > 0` via range-checked `s1_minus_one`; `s2_sign_bit` boolean
- [ ] `SELECTOR_RECON` packed rows reconstructing both scalars (`selector_i = a_i + 4·b_i` via `Selector4x4`)
- [ ] `selector_final` / `init_base_index` derivation; negative tests (mutated `s1`, flipped `s2_sign_bit`)

**Implementation Notes**: Steps 8–9 of the v8 order. The top-limb bounds are load-bearing — without `q[9] < 2¹¹` the scalar equation is satisfiable up to `2¹³⁰`, breaking integer soundness. Selector reconstruction proves `< 2¹²⁸` for free, so no separate range check is needed.

### 3.6 Prepared Table & PreparedPoint Copy Bus

**Description**: Construction of the 8-entry base table (plus `R3` and `Table[16]`) per certificate and the `PreparedPoint` LogUp copy bus that carries points to the chain.

**Requirements**:
- [ ] Table preparation EC schedule (`P3`, `R3`, `Base[0..7]`) with `STATE_LOAD` jumps; cert 0 specialised with preprocessed `[2]G`/`[3]G`
- [ ] `AFFINE_EXPORT` of each `Base[i]`, `R3`, `Table[16]`
- [ ] `Table[16]` construction pipeline (decode → fetch → negate → add → export)
- [ ] `PreparedPoint(sig_id, cert_id, table_index, x, y, inf)` relation with counted, range-bounded `use_count`
- [ ] `use_count = 0` explicitly constrained on inactive rows; copy-bus imbalance negative test

**Implementation Notes**: Steps 10–11 of the v8 order. `sig_id`/`cert_id` are preprocessed to prevent cross-signature table reuse. `R3` is *not* on the bus — it flows via fixed-schedule offset. Do not carry all 8 base points through every chain row (≈328 columns); the copy bus is the whole point.

### 3.7 Chain Execution, MSB/LSB Correction & Final Check

**Description**: The `DOUBLE,DOUBLE,ADD` scalar-mul chain, MSB initialisation, LSB correction, and the certificate + signature final checks.

**Requirements**:
- [ ] Chain rows with previous-row state transitions (`bit_reverse_coset_to_circle_domain_order`) and boundary indicators; inline operand selection via `Selector16Decode`
- [ ] `MSB_SELECT` (init from `init_base_index`); `LSB_SELECT` + `EC_ADD` with `lsb00_active` conditional `Base[2]` consumption
- [ ] Certificate final check: `Z_acc·Z_acc_inv = 1`, homogeneous cross-multiplication `X_acc = x_r3·Z_acc`, `R3` finite (`cert_active·inf_r3 = 0`)
- [ ] `FINAL_CHECK`: `R = H1 + H2`, `Z_R≠0`, `x(R) mod n = r`; optional recovery-id parity extraction
- [ ] Negative tests: chain coordinate mutation, projective-equiv bypass, `R = O`

**Implementation Notes**: Steps 12–14, 16 of the v8 order. 63 steps × 3 rows × 2 certs ≈ 378 chain rows. The chain invariant `Acc = R3` is a property of the Garaga recoding plus correct decoding — the `Z_acc_inv` check prevents a `(0,0,0)` Acc from silently passing cross-multiplication.

### 3.8 ECDSA Big-AIR Assembly, Public Binding & Zero Branch

**Description**: Assemble the `EcdsaVm` component — preprocessed selectors, materialised active gates, public-input binding, the zero-scalar branch — and wire prover/verifier.

**Requirements**:
- [ ] `PUBLIC_BIND` row with full input validation; `PublicEcdsaInstance` relation and `initial_logup_sum`
- [ ] Preprocessed row-type/`sig_id`/`cert_id`/`step_id` columns; materialised `sig_active`/`cert_active`/`cert_zero_active`/`lsb00_active` with defining constraints
- [ ] Zero-branch gating with explicit per-family disabled-row constraints (`cert_zero_active·limb = 0`)
- [ ] Replace the `stark.rs` stubs with real `prove_ecdsa_verification` / `verify_ecdsa_proof`
- [ ] Run the full v8 negative-test and edge-case suite (`S = 1, n−1, 3, n−3, 3⁻¹, −3⁻¹`; `u1 = 0` zero branch)

**Implementation Notes**: Steps 15, 17–19 of the v8 order. Active gates must be materialised witness columns, not inline products, to keep LogUp numerator degree at 1. This item makes `stwo-p256` a working standalone ECDSA prover before integration. Degree budget `D ≤ 4` — split any RCB formula that exceeds it.

### SHA-256 AIR

### 3.9 SHA-256 Compression & Multi-Block Hashing AIR

**Description**: The `stwo-sha256` crate — a SHA-256 AIR over M31 implementing compression, message scheduling, and multi-block hashing, per the validated 2.5 design.

**Requirements**:
- [ ] Bit-index-partitioned lookup tables for `Σ0`/`Σ1`/`σ0`/`σ1`, `ch`, `maj` (16-bit low/high M31 split)
- [ ] Round function and 64-round message schedule constraints
- [ ] Multi-block chaining (initial vector → block → updated state) for credential-sized inputs
- [ ] Padding constraints (length encoding, `0x80` marker)
- [ ] Native SHA-256 witness generator; property tests against the `sha2` crate including multi-block vectors
- [ ] Standalone prover/verifier for the SHA-256 component

**Implementation Notes**: Implement the *validated/corrected* design from `research/sha256-air-design.md` (2.5), not `docs/sha256_air_design.md` verbatim and not the `../sha256-air` reference verbatim. Used twice in the pipeline (`IssuerSignedItem` hash, COSE `Sig_structure` hash) — the digest-output columns must be cleanly exposable for LogUp binding in 3.12.

### mdoc Credential Parsing & Age Gadget

### 3.10 mdoc/CBOR Parsing & valueDigests Membership AIR

**Description**: The `stwo-mdoc` parsing layer — enough in-circuit CBOR decoding to locate the `IssuerSignedItem` `elementValue` and prove its digest is a member of the issuer-signed `valueDigests` map.

**Requirements**:
- [ ] In-circuit CBOR field extraction for `IssuerSignedItem` and the `MobileSecurityObject` `valueDigests` map
- [ ] `valueDigests` membership: the `IssuerSignedItem` SHA-256 digest equals a committed `valueDigests` entry
- [ ] LogUp binding of the digest produced by 3.9 to the membership check
- [ ] Native mdoc parser + test vectors from 2.4
- [ ] Negative tests: digest not in `valueDigests`, tampered `elementValue`

**Implementation Notes**: Constrain only the byte ranges the proof actually needs — full general CBOR parsing in-circuit is unnecessary and expensive. The 2.4 deliverable fixes the exact byte offsets/layout this gadget targets.

### 3.11 Birth-Date Extraction & Age-Over-18 Gadget AIR

**Description**: Parse the `birth_date` from the credential's `elementValue` and prove the holder's age against a public current date is at least 18.

**Requirements**:
- [ ] Parse the CBOR `full-date`/`tdate` birth date into year/month/day fields
- [ ] Age computation against the public `current_date`; integer comparison `age ≥ 18`
- [ ] Public-input columns for `current_date` and the age threshold
- [ ] Alternate path: verify the `age_over_18` boolean data element directly
- [ ] Tests: exactly-18 boundary, under-18 (must fail), leap-year birthdays

**Implementation Notes**: The birth date stays a private witness — only the boolean result is implied by proof validity. Boundary correctness (born exactly 18 years ago today) is the subtle case. The `birth_date` bytes must be the same bytes hashed in 3.9, bound via LogUp in 3.12.

### Pipeline Integration & Proving

### 3.12 Native End-to-End Witness Generator

**Description**: A native (out-of-circuit) generator that takes an mdoc credential + issuer key and produces the complete witness for the whole pipeline — the ground-truth oracle for the integrated trace.

**Requirements**:
- [ ] Compose the mdoc parser, SHA-256 witness generator, fake-GLV hint generator (2.3), and ECDSA witness into one pipeline witness
- [ ] Validate the witness end-to-end against `p256` + `sha2` before any proving
- [ ] Deterministic test-credential fixtures (valid over-18, valid exactly-18, invalid under-18, bad signature)
- [ ] Serde-serialisable witness type shared by all component trace generators

**Implementation Notes**: This is the spec's "extensive property-based testing against a reference implementation at every layer" risk mitigation. Build it before the Big AIR so integration debugging compares against a trusted witness, not a guess.

### 3.13 Pipeline Integration "Big AIR" & Prover/Verifier API + CLI

**Description**: The `eu-id-air` crate — compose the three component AIRs into one Stwo proof with the cross-component LogUp relations, and ship the demo CLI.

**Requirements**:
- [ ] Single-proof composition of `stwo-p256`, `stwo-sha256`, `stwo-mdoc` components
- [ ] LogUp relations binding: `IssuerSignedItem` digest ↔ `valueDigests` membership; `Sig_structure` digest ↔ ECDSA `z`; `birth_date` bytes ↔ SHA-256 preimage
- [ ] `prove_age_over_18` / `verify_age_over_18` library API
- [ ] `bin/` CLI: `eu-id prove`, `eu-id verify`, `eu-id bench`
- [ ] End-to-end test: valid credential proves, tampered/under-18 credential fails

**Implementation Notes**: Follow the `../falcon-air` `big_air` pattern (`claim` / `interaction_claim` / `relation` modules) — it is the production-grade reference for wiring multiple traces into one consistent proof. The cross-component binding is the soundness backbone; an unbound digest lets a prover mix values across components.

### Benchmarking & Dissemination

### 3.14 Laptop Benchmark Suite

**Description**: Criterion benchmarks producing the honest performance numbers the POC's argument rests on, on laptop hardware.

**Requirements**:
- [ ] Measure proof-generation time, proof size, peak memory, and verification time
- [ ] Per-component breakdown (SHA-256, ECDSA, mdoc) plus the full pipeline
- [ ] Run the simplest-component benchmark early (post-week-2 go/no-go gate per the PRD)
- [ ] Machine-readable results checked into `benches/results/`

**Implementation Notes**: The PRD's performance-risk mitigation is *benchmark early* — wire a benchmark for the SHA-256 component as soon as 3.9 lands, before the full system exists. If the primitives don't fit, narrow scope rather than ship a misleading result.

### 3.15 Mobile Benchmark Harness (iOS/Android)

**Description**: Cross-compile the prover for mobile and benchmark proof generation on real iOS and Android hardware — an MVP deliverable.

**Requirements**:
- [ ] Cross-compilation per 2.6: `cargo-ndk` (Android), iOS targets + `xcframework`
- [ ] FFI bindings and a thin `mobile/` harness app exposing prove + measure
- [ ] On-device measurement of proof-gen time and peak memory across a few representative devices
- [ ] `make bench-mobile` driving the harness; results in `benches/results/`

**Implementation Notes**: The PRD targets the FibRace bar — sub-5s STARK proofs on consumer phones. Memory ceiling is the headline risk: if proof generation exhausts phone RAM, that is a scope signal. Report device models and OS versions honestly alongside the numbers.

### 3.16 Technical Writeup & Topic G Submission

**Description**: The project's defining deliverable — a technical writeup comparing the POC to the zk-SNARK alternatives Topic G already considers, and a formal comment posted to EU GitHub Discussion #408 with proposed text additions.

**Requirements**:
- [ ] Writeup: what was built, honest benchmark numbers (laptop + mobile), and a comparison to BBS+/zk-SNARK on the same credential
- [ ] Explicit, honest disclosure that the first iteration is succinct-but-not-yet-zero-knowledge
- [ ] Proposed concrete text additions placing STARK-family schemes in the Topic G taxonomy
- [ ] Post the formal comment to Discussion #408 linking the open-source POC
- [ ] Polished public `README.md` with reproduction instructions and the research-prototype disclaimer

**Implementation Notes**: Frame the contribution as *additive, not adversarial* — filling a gap in the EU's analysis, not contesting their recommendations (PRD reception-risk mitigation). Minimum success is defined by this item: the POC works, produces honest numbers, and is on the public record.

---

## Phase 4: Nice to Have

### 4.1 Zero-Knowledge Masking

**Description**: Add zero-knowledge masking so the proof hides all witness information, upgrading the POC from succinct-only to fully zero-knowledge.

**Requirements**:
- [ ] Apply Stwo's ZK masking / blinding to the committed trace
- [ ] Verify proof size and timing impact and update the benchmark suite
- [ ] Update the writeup to reflect full ZK status
- [ ] Tests confirming witness values are not recoverable from the proof

**Implementation Notes**: The PRD explicitly defers this and discloses it honestly — the masking technique is well-understood in the literature. This is the natural second iteration and the most impactful credibility upgrade.

### 4.2 Proof-Size & Prover Optimization

**Description**: Reduce proof size and prover time once the correct baseline is measured — chiefly by batching chain steps.

**Requirements**:
- [ ] `QuadAdd`-style batching of `DOUBLE,DOUBLE,ADD` chain steps into wider rows
- [ ] Column-layout optimisation to keep `log_size = 9` (512 rows) per signature
- [ ] Re-benchmark against the 3.14 baseline
- [ ] Confirm the degree budget `D ≤ 4` still holds after batching

**Implementation Notes**: The v8 spec is explicit — do **not** batch until the baseline `DOUBLE/DOUBLE/ADD` implementation passes all tests and is profiled. Optimisation without a correct, measured baseline risks optimising a bug.

### 4.3 Multi-Signature / Batch Proving

**Description**: Prove multiple credential verifications in one proof, amortising fixed costs.

**Requirements**:
- [ ] Multi-signature row schedule in the `EcdsaVm` component
- [ ] Per-signature `sig_id` isolation in the `PreparedPoint` bus (already preprocessed)
- [ ] Benchmark amortised per-credential cost vs. single-proof
- [ ] Tests with mixed valid/invalid credentials in one batch

**Implementation Notes**: The v8 spec already includes `sig_id` in the `PreparedPoint` relation to prevent cross-signature table reuse — the design anticipates batching. Useful for verifiers checking many credentials.

### 4.4 SD-JWT VC Credential Format Support

**Description**: Support the IETF SD-JWT Verifiable Credential format alongside mdoc — the EU wallet's other credential format.

**Requirements**:
- [ ] SD-JWT VC parsing gadget (JSON / base64url) in `stwo-mdoc` or a sibling crate
- [ ] Selective-disclosure digest handling for SD-JWT
- [ ] Reuse the ECDSA + SHA-256 + age components unchanged
- [ ] Test vectors for SD-JWT VC credentials

**Implementation Notes**: SD-JWT VC is also ES256-signed, so the cryptographic core is reused — only parsing differs. Broadens the POC's relevance across EU wallet implementations.

### 4.5 Deterministic Shamir/Horner Fallback

**Description**: A deterministic double-scalar-multiplication path for when fake-GLV hints are unavailable.

**Requirements**:
- [ ] Horner-order width-5 double-scalar multiplication `[u1]G + [u2]Q`
- [ ] Preprocessed `G` digit-point tables; `QWindowTable` for the public key
- [ ] Selectable fake-GLV vs. deterministic mode
- [ ] Equivalence tests across both paths

**Implementation Notes**: Specified in the v8 spec as the fallback. Heavier (260 doublings + 104 mixed-adds) but needs no external hint generation — useful as a robustness baseline.

### 4.6 Production Hardening & Property-Based Test Expansion

**Description**: Hardening passes that elevate the prototype toward audit-readiness without claiming audit quality.

**Requirements**:
- [ ] Broad property-based test corpus across all components (random credentials, scalars, edge cases)
- [ ] Fuzzing of the CBOR/mdoc parser
- [ ] `tracing`-based structured logging and prover profiling instrumentation
- [ ] Document known limitations and the threat model

**Implementation Notes**: The PRD is explicit that this is a research prototype — the goal is honest, thorough testing, not an audit claim. Property tests against the native reference oracle are the core defence against silent soundness bugs.

---

## Phase 5: Future

### 5.1 Privacy-Preserving Revocation & Full Unlinkability

**Description**: Address the cryptographic properties the Topic G document discusses but the first iteration leaves out of scope.

**Features**:
- Privacy-preserving credential revocation (proving non-revocation without a tracking handle)
- Full unlinkability against issuer–verifier collusion
- Per-presentation freshness without correlatable identifiers

**Rationale**: These are first-class requirements in the Topic G analysis. Demonstrating STARKs can also satisfy them would move the contribution from "belongs in the candidate set" toward "competitive across the full property matrix."

### 5.2 Post-Quantum Migration Profile

**Description**: Lean into the STARK family's headline advantage by articulating a concrete post-quantum migration story for the wallet.

**Features**:
- PQ-secure issuer signatures replacing ES256 inside the same proof pipeline
- Alignment with ETSI PQ profiles and NIST-standardised PQ signature schemes
- A migration narrative: hash-based STARKs need no redesign as PQ pressure grows

**Rationale**: BBS+ and zk-SNARKs require redesign to survive PQ migration; STARKs are PQ-secure by default. As ETSI/NIST PQ work advances, a PQ-ready privacy technology becomes materially more valuable.

### 5.3 Wallet Integration SDK

**Description**: Package the prover as an SDK that a real EU-wallet implementation or Large Scale Pilot could evaluate.

**Features**:
- Stable library API and mobile bindings for wallet integration
- Credential-agnostic predicate interface
- Reference integration with an open-source wallet implementation

**Rationale**: Stretch success in the PRD is a Member State or Large Scale Pilot picking up STARK-based selective disclosure to evaluate. A clean SDK lowers the barrier from "interesting POC" to "thing we can try."

### 5.4 Broader Predicate & Credential Support

**Description**: Generalise beyond age-over-18 to the wider range of selective-disclosure predicates EU-wallet use cases need.

**Features**:
- Residency, licence-class, and other attribute predicates
- Range proofs and set-membership over credential attributes
- Composable multi-credential proofs

**Rationale**: Age-over-18 is the most-cited and easiest-to-grasp use case, which is why it is the POC. The same machinery generalises; demonstrating breadth strengthens the case that STARKs are a general-purpose answer, not a single-trick demo.
