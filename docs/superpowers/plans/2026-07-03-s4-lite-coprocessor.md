# S4-lite Coprocessor Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the S4-lite P-256 EC coprocessor in parallel with the current `stwo-p256` implementation, keeping the existing proof path as the default until the feature-gated coprocessor path passes soundness and performance gates.

**Architecture:** Add a new workspace crate, `eu-id-ec-coprocessor`, that owns native F_p256 arithmetic, transcript serialization, MLE utilities, layered sumcheck, mini-Ligero witness commitment, and ECDSA circuit/witness logic. Integration into `eu-id-prover` happens only behind the `ec-coprocessor` feature; the current `stwo-p256` path remains unchanged until BL6 is green.

**Tech Stack:** Rust 2021, `p256` for field arithmetic and test oracles, `blake2` for transcript-compatible hashing, existing workspace Stwo channel types at the integration boundary.

---

### Task 1: BL1 Crate And Field Layer

**Files:**
- Modify: `Cargo.toml`
- Create: `crates/eu-id-ec-coprocessor/Cargo.toml`
- Create: `crates/eu-id-ec-coprocessor/src/lib.rs`
- Create: `crates/eu-id-ec-coprocessor/src/field.rs`
- Create: `crates/eu-id-ec-coprocessor/src/channel.rs`
- Create: `crates/eu-id-ec-coprocessor/src/mle.rs`
- Create: `crates/eu-id-ec-coprocessor/tests/field.rs`
- Create: `crates/eu-id-ec-coprocessor/tests/mle.rs`

- [ ] Write failing tests for canonical `Fp` decoding at `p - 1`, `p`, `p + 1`, and `2^256 - 1`.
- [ ] Implement minimal `Fp` arithmetic, canonical serialization, challenge reduction, and batch inversion.
- [ ] Write failing tests for MLE padding, evaluation, equality polynomial, and first-variable fixing.
- [ ] Implement `Mle` utilities.
- [ ] Add channel wrapper helpers for deterministic byte mixing and `Fp` challenge drawing.
- [ ] Run `rtk proxy cargo test -p eu-id-ec-coprocessor`.

### Task 2: Non-Blocking Architect Mailbox

**Files:**
- Create: `tasks/parity/mailbox/questions/Q-s4-bl3-otp-final-algebra.md`
- Create: `tasks/parity/mailbox/questions/Q-s4-bl5-binding-spec.md`
- Create: `tasks/parity/mailbox/questions/Q-s4-g4-edge-ack.md`

- [ ] File BL3 question for the truncated Longfellow OTP final-relation algebra.
- [ ] File BL5 question requesting the G3-acked binding-argument spec.
- [ ] File G4 question requesting ack of the C9/C10 gate-charging re-derivation and C15 edge-completeness argument.
- [ ] Continue BL1/BL2 work without waiting for answers.

### Task 3: BL2 Layered Circuit And Sumcheck

**Files:**
- Create: `crates/eu-id-ec-coprocessor/src/circuit.rs`
- Create: `crates/eu-id-ec-coprocessor/src/sumcheck.rs`
- Create: `crates/eu-id-ec-coprocessor/tests/sumcheck.rs`

- [ ] Add tests for sparse `QuadTerm` evaluation against brute force on small circuits.
- [ ] Implement `Layer`, `Circuit`, `Witness`, and `q_tilde_eval`.
- [ ] Add prove/verify tests for a small satisfied circuit and a tampered witness.
- [ ] Implement per-layer sumcheck transcript with exported `InputClaims`.
- [ ] Add adversarial tests for coefficient, witness, round-polynomial, transcript-order, and final-claim mutations.

### Task 4: BL3 Mini-Ligero Commitment

**Files:**
- Create: `crates/eu-id-ec-coprocessor/src/rs.rs`
- Create: `crates/eu-id-ec-coprocessor/src/merkle.rs`
- Create: `crates/eu-id-ec-coprocessor/src/ligero.rs`
- Create: `crates/eu-id-ec-coprocessor/tests/ligero.rs`

- [ ] Add RS encode/open tests for rate-1/4 rows.
- [ ] Implement naive Lagrange row encoding for `k = 64`, `n = 256`.
- [ ] Add Merkle commit/open tests and corrupt-column rejection.
- [ ] Implement column commitment/opening and proximity checks.
- [ ] Add parameter computation code and tests proving configured parameters reach at least 128-bit soundness.
- [ ] Leave OTP final-relation code gated until the mailbox answer lands; continue non-OTP opening and input-claim tie-back.

### Task 5: BL4 ECDSA Witness And Circuit

**Files:**
- Create: `crates/eu-id-ec-coprocessor/src/ecdsa.rs`
- Create: `crates/eu-id-ec-coprocessor/src/hints.rs`
- Create: `crates/eu-id-ec-coprocessor/tests/ecdsa.rs`

- [ ] Add layout tests asserting `LAYOUT` length is exactly 2159.
- [ ] Add deterministic witness tests from real `p256` crate signatures.
- [ ] Implement `generate_witness` using `p256` as oracle and no RNG/threading.
- [ ] Add per-family negative tests from G4 C1-C15.
- [ ] Implement circuit-builder constraints in G4 inventory order.
- [ ] Print and assert gate count is at most 35,000; mailbox if it exceeds 33,000.

### Task 6: BL6 Feature-Gated Integration

**Files:**
- Modify: `Cargo.toml`
- Modify: `crates/eu-id-prover/Cargo.toml`
- Modify: `crates/eu-id-prover/src/lib.rs`
- Modify: `crates/eu-id-prover/src/generator.rs`
- Add integration tests under `crates/eu-id-prover/tests/`

- [ ] Add `ec-coprocessor` feature without changing default behavior.
- [ ] Add proof struct field for `CoprocessorProof` only under the feature.
- [ ] Replace P-256 module construction with coprocessor proof generation only under the feature.
- [ ] Add transcript-phase digest tests for prover/verifier order.
- [ ] Add cross-layer negatives: wrong `z`, swapped coprocessor proof, reordered transcript, and Ligero substitution.
- [ ] Run feature-off pinned behavior tests and feature-on e2e fixture tests.

## Self-Review

- Spec coverage: BL1-BL6 are represented; BL5 is intentionally represented by a mailbox-gated task because the S4 README says the spec arrives with the G3 ack.
- Placeholder scan: no task uses `TBD`; the only gated item is explicitly tied to a required mailbox answer.
- Scope check: the current implementation starts with BL1 and proceeds to independent BL2 work while architect-owned answers are pending.
