# eu-id — Project Specification

STARK-based zero-knowledge proofs for the EU Digital Identity Wallet.

## Project Overview

**Name:** eu-id

**Purpose:** A working, open-source proof-of-concept demonstrating that STARK proofs can perform privacy-preserving selective disclosure on real EU-wallet credentials — specifically, proving *"I am over 18"* from a digitally signed identity credential without revealing the holder's date of birth.

**Problem statement:** The European Commission's *Topic G* working document (the public decision process for which zero-knowledge technologies the EU Digital Identity Wallet will recommend) analyses two ZKP families — BBS+ signatures and zk-SNARKs — and omits STARKs entirely. STARKs offer post-quantum security by default, require no trusted setup, and have proven production scalability. This project produces the smallest credible technical artifact showing STARKs belong in that candidate set, and submits it to the public discussion (GitHub Discussion #408) with proposed text additions.

**Target users:** EU Commission Topic G working group, Member State wallet implementers, Large Scale Pilot projects, and cryptography researchers contributing to the standardisation process. The artifact itself is a research prototype, not a production library.

**Scope discipline (from the PRD):** This is a research prototype. We are *not* building a wallet, *not* building a production prover, and *not* claiming STARKs should replace BBS+/zk-SNARKs — only that they belong in the comparison. The first iteration produces **succinct** proofs (small, fast to verify) but not yet **zero-knowledge** proofs (ZK masking of the witness is a well-understood follow-up, deferred to Phase 4 and disclosed honestly in the writeup).

See `docs/zk_digitalid_prd.md` for the full product rationale and `crates/stwo-p256/docs/p256_fake_glv_air_full_spec.md` for the frozen v8 AIR specification of the ECDSA component.

## Architecture

### The demonstration

An ISO/IEC 18013-5 **mdoc** credential (the format used by EU-wallet mobile driving licences and PID) is signed by an issuer using **ES256** — ECDSA over NIST P-256 with SHA-256. The credential body contains the holder's `birth_date` as an `IssuerSignedItem`; its SHA-256 digest is committed inside the issuer-signed `MobileSecurityObject` (MSO).

The wallet holder wants to prove to a verifier: *"an issuer I trust signed a credential asserting my age, and that age is ≥ 18"* — while keeping the actual birth date private.

### Proof pipeline (single STARK proof)

```text
PRIVATE WITNESS (never leaves the wallet)
  - IssuerSignedItem bytes containing birth_date
  - MobileSecurityObject (MSO) bytes
  - ECDSA signature (r, s)
  - fake-GLV hints (s1, s2_abs, s2_sign_bit) per scalar-mul certificate

PUBLIC INPUTS (revealed to the verifier)
  - issuer public key (P-256 affine point)
  - current date / age threshold (18 years)
  - the statement being proved

       +---------------------------------------------------------------+
       |                    eu-id Big AIR (one proof)                  |
       |                                                               |
       |  [1] stwo-sha256 : SHA-256(IssuerSignedItem) -> elementDigest  |
       |            |                                                  |
       |  [2] stwo-mdoc   : elementDigest in MSO.valueDigests           |
       |            |        (CBOR membership)                         |
       |  [3] stwo-sha256 : SHA-256(COSE Sig_structure over MSO) -> z   |
       |            |                                                  |
       |  [4] stwo-p256   : ECDSA-P256 verify (z, r, s, issuerPubKey)   |
       |            |        via Garaga-style fake-GLV certificates     |
       |            |                                                  |
       |  [5] stwo-mdoc   : parse birth_date, age(current_date) >= 18   |
       +---------------------------------------------------------------+
                                   |
                                   v
                    STARK proof + public inputs
                                   |
                                   v
                 Verifier: accept  =>  holder is over 18,
                 credential issuer-signed, DOB not disclosed
```

### Cross-component data flow

All sub-AIRs live as components inside one Stwo proof and are wired together with **LogUp relations** so that values flow soundly between them:

- The SHA-256 digest of the `IssuerSignedItem` is bound, limb-by-limb, to the membership check against `MSO.valueDigests`.
- The SHA-256 digest of the COSE `Sig_structure` is bound to the `z` public-input of the ECDSA component (`PublicEcdsaInstance` relation).
- The `birth_date` bytes consumed by the age gadget are bound to the SHA-256 preimage that produced `elementDigest`, so the holder cannot prove age from one date while hashing another.

This binding is the soundness backbone: it prevents a prover from satisfying each component in isolation with mismatched values.

## Tech Stack

| Layer | Choice | Rationale |
|---|---|---|
| Language | Rust (nightly, pinned via `rust-toolchain.toml`) | Stwo requires nightly (`portable_simd`); existing scaffold pins `nightly-2025-07-14`. |
| Proof system | [Stwo](https://github.com/starkware-libs/stwo) — Circle STARK over Mersenne-31 (M31) | Post-quantum (hash-based), no trusted setup, fast on consumer hardware (FibRace: sub-5s proofs on 1,400 phone models). The framework this POC argues for. |
| Constraint framework | `stwo-constraint-framework` | `FrameworkEval` / `EvalAtRow` AIR authoring; LogUp batching. |
| Field representation | 13-bit limbs × 20 (P-256 256-bit values); M31 base field | `20·(2¹³−1)² < 2³¹` keeps schoolbook products inside M31 with headroom. |
| EC scalar mul | Garaga-style **fake-GLV** certificates; RCB homogeneous-projective formulas | Verifies each scalar mul with small signed components instead of full 256-bit chains; RCB Algorithms 5/6 are exception-free. |
| Reference / test deps | `p256`, `ecdsa`, `sha2`, `rand`, `hex` | Native ground-truth oracle for property-based testing at every layer. |
| Benchmarking | `criterion` (laptop); `cargo-ndk` / `cargo-lipo` + FFI harness (mobile) | Proof-gen time, proof size, memory, verify time on laptop **and** mobile (MVP requirement). |
| Tooling | Makefile, Docker + docker-compose, GitHub Actions | Reproducible builds and CI per workspace conventions. |

## Project Structure

Cargo workspace; each major component is its own crate under `crates/`.

```text
eu-id/
├── Cargo.toml                 # workspace manifest
├── rust-toolchain.toml        # pinned nightly
├── Makefile                   # dev / run / test / check / bench / mobile targets
├── Dockerfile
├── docker-compose.yml
├── crates/
│   ├── stwo-p256/             # EXISTS — ECDSA P-256 verification AIR + native reference
│   │   ├── docs/p256_fake_glv_air_full_spec.md   # frozen v8 AIR spec
│   │   └── src/{types,limbs,field_ops,curve,ecdsa,trace,constraints,stark}.rs
│   ├── stwo-sha256/           # NEW — SHA-256 AIR (M31 lookup-table design)
│   ├── stwo-mdoc/             # NEW — mdoc/CBOR parsing + valueDigests membership + age gadget
│   └── eu-id-air/             # NEW — integration "Big AIR" wiring all components
├── bin/                       # demo CLI prover/verifier
├── benches/                   # criterion benchmark suite
├── mobile/                    # iOS/Android benchmark harness (FFI bindings)
├── scripts/                   # bash helpers (test vectors, credential generation)
├── research/                  # Phase 2 research deliverables
└── docs/
    ├── SPEC.md                # this file
    ├── ROADMAP.md
    ├── zk_digitalid_prd.md    # product requirements
    └── sha256_air_design.md   # SHA-256 M31 decomposition notes
```

## Core Modules

### `crates/stwo-p256` — ECDSA P-256 Verification AIR

The technically hardest component. The native reference layer is **already implemented and tested**; the AIR is the build target.

- **`types.rs`, `limbs.rs`** *(done)* — `U256`, P-256 constants, `LimbsM31` (13-bit limb decomposition), schoolbook multiplication, carry propagation.
- **`field_ops.rs`** *(done)* — `mul_mod` / `add_mod` / `sub_mod` native witness generators with 512-bit big-integer helpers.
- **`curve.rs`, `ecdsa.rs`** *(done)* — native point arithmetic, `mod_inverse`, textbook ECDSA verification validated against the `p256` crate. These are the out-of-circuit oracle; the in-circuit path uses fake-GLV + RCB instead.
- **`trace.rs`, `constraints.rs`, `stark.rs`** *(stubs — primary work)* — trace generation, the `EcdsaVm` AIR component, and prover/verifier wiring per the v8 spec.

The v8 spec defines a single dynamic `EcdsaVm` component with static lookup tables (`Range13/9/11/128`, selector tables), homogeneous-projective EC state, fake-GLV certificates, a `PreparedPoint` copy bus, and a `DOUBLE,DOUBLE,ADD` chain. It carries a **M31 headroom audit blocker** that must be discharged in Phase 2 research before any arithmetic row type is sound.

### `crates/stwo-sha256` — SHA-256 AIR

Proves SHA-256 compression and message scheduling over M31, using the bit-index-partitioned lookup-table design sketched in `docs/sha256_air_design.md`. Used twice in the pipeline: once to hash the `IssuerSignedItem`, once to hash the COSE `Sig_structure`. Must support multi-block messages. The reference `../sha256-air` project is a learning artifact only — its decomposition is to be validated, not copied (Phase 2 research item).

### `crates/stwo-mdoc` — Credential Parsing & Age Gadget AIR

- CBOR parsing of the `IssuerSignedItem` and `MobileSecurityObject` sufficient to extract `elementValue` (`birth_date`) and the `valueDigests` map.
- `valueDigests` membership: proves the `IssuerSignedItem` digest appears in the issuer-signed MSO.
- Age-over-18 gadget: parses the `full-date` / `tdate` birth date, computes the holder's age against a public current date, and asserts `age ≥ 18` as an integer comparison.

### `crates/eu-id-air` — Integration Big AIR

Composes the three component AIRs into one Stwo proof, declares the LogUp relations binding them (digest ↔ `z`, preimage ↔ parsed bytes), and exposes the end-to-end prover/verifier API. Pattern reference: `../falcon-air`'s `big_air` module (production-grade `claim` / `interaction_claim` / `relation` wiring).

## Data Models

### Native types (in `stwo-p256`, partly done)

- `U256` — 256-bit integer, big-endian bytes.
- `LimbsM31` — 20 × 13-bit limbs as M31 values, little-endian limb order.
- `AffinePoint` — P-256 affine point; projective `(X, Y, Z)` RCB state for in-circuit EC.
- `EcdsaVerifyInput` / `EcdsaVerifyWitness` — message digest, signature, public key, and all intermediates.
- `MulModWitness` / `AddModWitness` / `SubModWitness` — modular-arithmetic witness records (carries, quotients, reduction flags).

### Credential types (new, in `stwo-mdoc`)

- `MobileSecurityObject` — `docType`, `valueDigests` (map of `digestID → SHA-256 digest`), `validityInfo`, `deviceKeyInfo`.
- `IssuerSignedItem` — `digestID`, `random` salt, `elementIdentifier`, `elementValue`.
- `CoseSign1` — protected header, payload (the MSO), and the ES256 signature `(r, s)`.

### Public input contract

`PublicEcdsaInstance(z[20], r[20], s[20], pub_x[20], pub_y[20])` binds the ECDSA component's public tuple via LogUp (provider yields `-1`, the `PUBLIC_BIND` row consumes `+sig_active`). The Big AIR adds public columns for the issuer key, current date, and age threshold.

## Public Interface

CLI demo binary in `bin/`:

```text
eu-id prove   --credential <mdoc.cbor> --issuer-key <pubkey> --out proof.bin
eu-id verify  --proof proof.bin --issuer-key <pubkey> --current-date <YYYY-MM-DD>
eu-id bench   [--mobile]
```

Library API in `eu-id-air`: `prove_age_over_18(witness, config) -> Proof` and `verify_age_over_18(proof, public_inputs) -> bool`. Per-component prover/verifier entry points remain available for testing.

## External Integrations

- **Stwo framework** — consumed as a git dependency (`starkware-libs/stwo`), `prover` feature. Pinned via `Cargo.lock`.
- **EU GitHub Discussion #408 (Topic G)** — the dissemination target; the project's final deliverable is a formal comment linking the POC with proposed Topic G text additions.
- **Garaga** *(reference, optional)* — source of the fake-GLV recoding/hint algorithm. Hint generation (lattice reduction producing `s1, s2_abs, s2_sign_bit`) is implemented natively in Rust; Garaga-generated hints are used as a cross-check oracle.
- **`p256` / `ecdsa` / `sha2` crates** — dev-only ground-truth oracles.

## Key Decisions

1. **Full in-circuit pipeline.** The credential body is a private witness; SHA-256, ECDSA verification, and the age comparison all run inside the circuit. The only public values are the issuer key, the date, and the statement. (Considered: taking the digest `z` as a public input — rejected because it weakens the "from a real credential" claim.)
2. **ISO mdoc / ES256 credential format.** mdoc is the format EU-wallet mDLs actually use and is directly signed with P-256 + SHA-256, making the POC maximally credible to the Topic G audience. SD-JWT VC support is deferred to Phase 4.
3. **Fake-GLV certificates over deterministic double-scalar-mul.** Verifies `[u1]G` and `[u2]Q` with small signed components instead of two full 256-bit chains. A deterministic Shamir/Horner fallback is specified for the hint-unavailable case (Phase 4).
4. **Homogeneous-projective (RCB) coordinates, not Jacobian.** RCB Algorithms 5/6 are exception-free; homogeneous affine recovery (`x = X/Z`) costs one fewer multiplication than Jacobian.
5. **Single "Big AIR".** All dynamic rows share one physical Stwo component to minimise committed columns (proof size scales with total columns). Static lookup tables are separate components.
6. **Succinct first, zero-knowledge second.** The first iteration omits ZK masking and discloses this honestly; masking is a well-understood Phase 4 addition.
7. **M31 headroom audit is a research blocker.** Every big-integer constraint equation must be machine-checked to not alias to zero in M31 before its row type is considered sound (Phase 2 research deliverable).
8. **Native reference layer is the test oracle.** Property-based testing against `p256`/`sha2` and the native witness generators at every layer — the mitigation for silent cryptographic bugs that pass tests but break soundness.
