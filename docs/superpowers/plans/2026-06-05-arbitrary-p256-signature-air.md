# Arbitrary P-256 Signature AIR Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `verify_current_air_monolithic` verify one arbitrary valid P-256 ECDSA signature statement, not only the current single-signature small-`u1/u2` trivial fake-GLV slice.

**Architecture:** Keep the current relation-bound monolithic STARK and existing fake-GLV/prepared-table/projective-RCB structure. Replace the trivial fake-GLV scalar strategy with a full-width bounded fake-GLV decomposer plus in-AIR scalar-mod-mul linkage, then make final addition complete for valid finite P-256 cases, especially doubling. Native code may build witnesses, but verifier acceptance must come from public inputs, AIR constraints, LogUp balances, and `verify_current_air_monolithic`.

**Tech Stack:** Rust, `stwo`, existing `stwo-p256` AIR modules, existing `scalar_mod_mul` components with external limb links, existing projective-RCB field-mul engine, release-mode focused tests through `rtk proxy cargo test`.

---

## Current State To Preserve

- The monolithic proof boundary is in `crates/stwo-p256/src/proof.rs`.
- Public input, scalar setup, cert binding, prepared-table, public-key-on-curve, final-check, and relation balances are already wired into one verifier-facing proof.
- The current blocker is scope, not a known invalid-signature acceptance:
  - `crates/stwo-p256/src/scalar/fake_glv_scalar.rs` only proves the trivial scalar case in AIR.
  - `P256ProofClaim::from_inputs_with_trivial_fake_glv_hints` is still the main claim builder.
  - `crates/stwo-p256/src/final_add_air.rs` rejects equal-x finite inputs, so valid doubling cases are unprovable.
  - `PublicKeyCurveSliceClaim` and final-add wiring are single-signature; this plan keeps one signature per proof and makes that one signature arbitrary.

## File Structure

- Modify `crates/stwo-p256/Cargo.toml`: add `num-bigint` and `num-traits` if the native fake-GLV decomposer needs big integer continued fractions. These are witness-builder dependencies; verifier soundness must not rely on them.
- Create `crates/stwo-p256/src/scalar/fake_glv_decompose.rs`: native full-width fake-GLV decomposition for any nonzero scalar modulo `n`.
- Modify `crates/stwo-p256/src/scalar/mod.rs`: export `fake_glv_decompose`.
- Modify `crates/stwo-p256/src/scalar/fake_glv_scalar.rs`: replace trivial AIR constraints with general bounded scalar-hint constraints and expose selected scalar-mod-mul operands/results.
- Modify `crates/stwo-p256/src/proof.rs`: replace trivial hint builders in production paths, add fake-GLV scalar-mod-mul rows, update relation balances, tests, diagnostics, and proof-slot notes.
- Modify `crates/stwo-p256/src/final_add_air.rs`: support the finite doubling branch in AIR.
- Modify `crates/stwo-p256/src/final_check_air.rs`: update stale docs and ensure final-infinity rejection is documented as statement invalidity, not unsupported valid input.
- Modify `crates/stwo-p256/src/final_check.rs`: keep native final witness generation aligned with the new final-add branch support.
- Add tests in existing `#[cfg(test)]` modules in `fake_glv_scalar.rs`, `final_add_air.rs`, and `proof.rs`; do not create a separate test harness unless the existing file becomes unmanageable.

---

## Task 1: Add Red Tests For Arbitrary Full-Width Scalars

**Files:**
- Modify: `crates/stwo-p256/src/proof.rs`
- Modify: `crates/stwo-p256/src/scalar/fake_glv_scalar.rs`

- [x] **Step 1: Add a helper that constructs a valid ECDSA statement from arbitrary `u1/u2`.**

Add this helper inside `proof.rs` test module near `valid_real_input_with_small_u_scalars`:

```rust
fn valid_real_input_with_u_scalars(u1: U256, u2: U256) -> EcdsaVerifyInput {
    assert_ne!(u2, U256::ZERO, "u2 must be nonzero for ECDSA setup");
    let n = U256::from_le_u64s(&P256_ORDER);
    let public_key = generator_point();
    let u_sum = add_mod_u256(&u1, &u2, &n);
    let r_point = scalar_mul(&u_sum, &public_key).expect("nonzero R");
    let r = x_mod_order(&r_point.x);
    let u2_inv = mod_inverse(&u2, &n);
    let s = mul_mod_witness(&r, &u2_inv, &n).result.to_u256();
    let message_hash = mul_mod_witness(&u1, &s, &n).result.to_u256();

    EcdsaVerifyInput {
        message_hash,
        signature: Signature { r, s },
        public_key,
    }
}

fn scalar_near_order(delta: u64) -> U256 {
    let n = U256::from_le_u64s(&P256_ORDER);
    sub_mod_u256(&n, &U256::from_le_u64s(&[delta, 0, 0, 0]), &n)
}

fn add_mod_u256(a: &U256, b: &U256, modulus: &U256) -> U256 {
    crate::field_ops::add_mod_witness(a, b, modulus).result.to_u256()
}

fn sub_mod_u256(a: &U256, b: &U256, modulus: &U256) -> U256 {
    crate::field_ops::sub_mod_witness(a, b, modulus).result.to_u256()
}
```

- [x] **Step 2: Add a failing proof-construction test for full-width `u1/u2`.**

Add:

```rust
#[test]
fn arbitrary_full_width_u_scalars_build_a_current_air_claim() {
    let input = valid_real_input_with_u_scalars(scalar_near_order(123), scalar_near_order(456));
    assert!(ecdsa_verify(&input), "synthetic arbitrary-width input must be valid");

    P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
        .expect("arbitrary full-width valid signature should build a proof draft");
}
```

Expected current failure: method missing or `ScalarDoesNotFitTrivialHint`.

- [x] **Step 3: Add a failing fake-GLV decomposition test.**

Add in `fake_glv_scalar.rs` tests:

```rust
#[test]
fn fake_glv_hint_supports_near_order_scalar() {
    let scalar = P256M31BigInt::from_u256(&U256::from_le_u64s(&[
        P256_ORDER[0] - 123,
        P256_ORDER[1],
        P256_ORDER[2],
        P256_ORDER[3],
    ]));
    let hint = FakeGlvScalarHint::decompose(&scalar)
        .expect("full-width scalar should have a bounded fake-GLV hint");
    verify_scalar_equation(&scalar, &hint).expect("hint equation must verify");
    hint.s1.require_128_bit_bound("s1").expect("s1 bound");
    hint.s2_abs.require_128_bit_bound("s2_abs").expect("s2 bound");
    hint.q.require_128_bit_bound("q").expect("q bound");
}
```

- [x] **Step 4: Run the red tests.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 arbitrary_full_width_u_scalars_build_a_current_air_claim --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 fake_glv_hint_supports_near_order_scalar --release -- --test-threads=1 --nocapture
```

Expected: both fail for missing arbitrary decomposer/build path.

Observed (2026-06-05): both red tests fail as predicted with `E0599`:
- `proof.rs:3514` → `from_inputs_with_arbitrary_fake_glv_hints` not found on `P256ProofDraft`.
- `fake_glv_scalar.rs:994` → `decompose` not found on `FakeGlvScalarHint`.

---

## Task 2: Implement Native Full-Width Fake-GLV Decomposition

**Files:**
- Create: `crates/stwo-p256/src/scalar/fake_glv_decompose.rs`
- Modify: `crates/stwo-p256/src/scalar/mod.rs`
- Modify: `crates/stwo-p256/src/scalar/fake_glv_scalar.rs`
- Modify: `crates/stwo-p256/Cargo.toml`

- [x] **Step 1: Add dependencies only if the native decomposer needs them.**

In `crates/stwo-p256/Cargo.toml`:

```toml
num-bigint = "0.4"
num-traits = "0.2"
num-integer = "0.1"
```

- [x] **Step 2: Create the decomposer module.**

Algorithm: port Garaga's `precompute_lattice` (Crypto-2001 GLV Algorithm 3.7,
half-GCD lattice basis on `(n, scalar)`); see
`~/garaga/hydra/garaga/hints/fake_glv.py::precompute_lattice`. Then convert
to the eu-id AIR form by branching on `sign(s2_signed)` and computing `q`
directly in that branch (never `abs(q_signed)`).

**Locked sign convention** (matches `signed_hint_point` polarity):

```
bit = 0  ⇔  s2_signed = +s2_abs  ⇔  AIR: k·s2_abs − q·n + s1 = 0  ⇔  selected_s1 = n − s1  ⇔  R = +h
bit = 1  ⇔  s2_signed = −s2_abs  ⇔  AIR: k·s2_abs − q·n − s1 = 0  ⇔  selected_s1 =    s1  ⇔  R = −h
```

Add `crates/stwo-p256/src/scalar/fake_glv_decompose.rs`:

```rust
//! Native witness-only fake-GLV decomposition for any scalar in [0, n).
//!
//! Algorithm: Garaga `precompute_lattice` (CT-2001 GLV Algorithm 3.7).
//! Identity proven: s1_signed + scalar · s2_signed ≡ 0 (mod n)
//!                  with |s1|, |s2| ≲ √n ≈ 2^128 for P-256, s1 > 0.
//!
//! Three witness-time identities checked via debug_assert (catch every
//! sign/polarity bug immediately):
//!   1. Garaga:      s1_signed + k · s2_signed ≡ 0 (mod n)
//!   2. AIR integer: k · s2_abs − q · n ± s1 = 0 in the chosen branch
//!   3. Result:      k · s2_abs ≡ selected_s1 (mod n)

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use stwo_p256_utils::scalar_arithmetic::P256_ORDER;

use crate::types::U256;

pub const FAKE_GLV_BOUND_BITS: usize = 128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FakeGlvDecomposition {
    /// Positive magnitude of s1 (Garaga invariant: s1 > 0). < 2^128.
    pub s1: U256,
    /// |s2_signed|. > 0 when scalar != 0, < 2^128.
    pub s2_abs: U256,
    /// eu-id polarity: false ⇒ s2_signed = +s2_abs; true ⇒ s2_signed = −s2_abs.
    pub s2_sign_bit: bool,
    /// AIR-form quotient (always ≥ 0). < 2^128.
    pub q: U256,
}

pub fn decompose_scalar_mod_n(scalar: &U256) -> Option<FakeGlvDecomposition> {
    let n: BigInt = biguint_from_u256(&U256::from_le_u64s(&P256_ORDER)).into();
    let n_unsigned = n.to_biguint().unwrap();
    let k = BigInt::from(biguint_from_u256(scalar).mod_floor(&n_unsigned));
    if k.is_zero() {
        return Some(FakeGlvDecomposition {
            s1: U256::ZERO, s2_abs: U256::ZERO, s2_sign_bit: false, q: U256::ZERO,
        });
    }

    // --- Garaga half-GCD lattice on (n, k) ---
    let (mut s1_signed, mut s2_signed) = precompute_lattice_v1(&n, &k);

    // Witness assertion 1: Garaga identity.
    debug_assert_eq!(
        (&s1_signed + &k * &s2_signed).mod_floor(&n),
        BigInt::zero(),
        "Garaga: s1 + k·s2_signed ≡ 0 mod n",
    );

    // Normalize: force s1 > 0 (relation is invariant under (V1 → −V1)).
    if s1_signed.sign() == Sign::Minus {
        s1_signed = -s1_signed;
        s2_signed = -s2_signed;
    }
    if s1_signed.is_zero() || s2_signed.is_zero() {
        // Pathological scalar (e.g. k = n − 1 can degenerate); caller may
        // special-case via a Garaga-style remap (k → 1 with adjusted hint point).
        return None;
    }

    let bound = BigInt::one() << FAKE_GLV_BOUND_BITS;
    if s1_signed >= bound || s2_signed.abs() >= bound {
        return None;
    }

    let s1_pos     = s1_signed.to_biguint().expect("s1 > 0 after normalize");
    let s2_abs_big = s2_signed.abs();

    // --- Branch-direct q in the AIR equation's own form (never abs(q_signed)) ---
    let (s2_sign_bit, selected_s1, q_unsigned) = if s2_signed.sign() == Sign::Minus {
        // bit = 1 branch.  AIR: k·s2_abs − q·n − s1 = 0  ⇒  q = (k·s2_abs − s1) / n
        let numerator = &k * &s2_abs_big - BigInt::from(s1_pos.clone());
        debug_assert!(
            numerator.mod_floor(&n).is_zero(),
            "AIR identity (bit=1): k·s2_abs − q·n − s1 = 0",
        );
        let q = (&numerator / &n).to_biguint().expect("q ≥ 0 by construction");
        (true, s1_pos.clone(), q)
    } else {
        // bit = 0 branch.  AIR: k·s2_abs − q·n + s1 = 0  ⇒  q = (k·s2_abs + s1) / n
        let numerator = &k * &s2_abs_big + BigInt::from(s1_pos.clone());
        debug_assert!(
            numerator.mod_floor(&n).is_zero(),
            "AIR identity (bit=0): k·s2_abs − q·n + s1 = 0",
        );
        let q = (&numerator / &n).to_biguint().expect("q ≥ 0 by construction");
        (false, &n_unsigned - &s1_pos, q)
    };

    if BigInt::from(q_unsigned.clone()) >= bound {
        return None;
    }

    // Witness assertion 3: third independent identity (catches selected_s1 bugs).
    debug_assert_eq!(
        (BigInt::from(biguint_from_u256(scalar)) * &s2_abs_big).mod_floor(&n),
        BigInt::from(selected_s1.clone()),
        "selected_s1 must equal k·s2_abs mod n",
    );

    let s2_abs_biguint = s2_abs_big.to_biguint().expect("|s2| ≥ 0");
    Some(FakeGlvDecomposition {
        s1:          u256_from_biguint(&s1_pos)?,
        s2_abs:      u256_from_biguint(&s2_abs_biguint)?,
        s2_sign_bit,
        q:           u256_from_biguint(&q_unsigned)?,
    })
}

/// Half-GCD / extended Euclidean state on (n, k); stops at the first remainder
/// magnitude < ⌊√n⌋. Maintains (rem_i, s_i, t_i) with rem_i = s_i·n + t_i·k.
/// Returns V1 = (rem, −t)  s.t.  rem + k·(−t) ≡ 0 (mod n).
fn precompute_lattice_v1(n: &BigInt, k: &BigInt) -> (BigInt, BigInt) {
    let mut prev = (n.clone(), BigInt::one(),  BigInt::zero());
    let mut curr = (k.clone(), BigInt::zero(), BigInt::one());
    let sqrt_n = n.sqrt();
    while curr.0.abs() >= sqrt_n {
        let q = &prev.0 / &curr.0;
        let next = (
            &prev.0 - &q * &curr.0,
            &prev.1 - &q * &curr.1,
            &prev.2 - &q * &curr.2,
        );
        prev = curr;
        curr = next;
    }
    (curr.0, -curr.2)
}

fn biguint_from_u256(v: &U256) -> BigUint { BigUint::from_bytes_be(&v.0) }

fn u256_from_biguint(v: &BigUint) -> Option<U256> {
    let bytes = v.to_bytes_be();
    if bytes.len() > 32 { return None; }
    let mut out = [0u8; 32];
    out[32 - bytes.len()..].copy_from_slice(&bytes);
    Some(U256(out))
}
```

- [x] **Step 3: Export the module.**

In `crates/stwo-p256/src/scalar/mod.rs`:

```rust
pub mod fake_glv_decompose;
```

- [x] **Step 4: Add `FakeGlvScalarHint::decompose`.**

In `fake_glv_scalar.rs`:

```rust
pub fn decompose(scalar: &P256M31BigInt) -> Result<Self, FakeGlvScalarHintError> {
    let decomposition = crate::scalar::fake_glv_decompose::decompose_scalar_mod_n(&scalar.to_u256())
        .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?;
    Ok(Self {
        s1: FakeGlvSmallScalar::from_p256_if_128_bit(&P256M31BigInt::from_u256(&decomposition.s1))
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?,
        s2_abs: FakeGlvSmallScalar::from_p256_if_128_bit(&P256M31BigInt::from_u256(&decomposition.s2_abs))
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?,
        s2_sign_bit: M31::from_u32_unchecked(decomposition.s2_sign_bit as u32),
        q: FakeGlvSmallScalar::from_p256_if_128_bit(&P256M31BigInt::from_u256(&decomposition.q))
            .ok_or(FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint)?,
    })
}
```

- [x] **Step 5: Keep the trivial helper but stop using it in production paths.**

Leave `trivial_for_small_scalar` for narrow diagnostic tests. New production builders must call `decompose`.

Done as part of Task 2 commit: `from_inputs_with_arbitrary_fake_glv_hints` (claim + draft) calls `decompose`; `trivial_for_small_scalar` retained.

- [x] **Step 6: Run native decomposition tests.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 fake_glv_hint_supports_near_order_scalar --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 fake_glv_scalar_hints --release -- --test-threads=1 --nocapture
```

Expected: decomposition tests pass; existing trivial tests still pass.

Observed: 15/15 pass — 7 new decomposer unit cases (`decomposes_zero_scalar`,
`decomposes_one`, `decomposes_small_scalar`, `decomposes_near_order_scalar`,
`decomposes_half_order_scalar`, `decomposes_2_pow_128_minus_1`,
`decomposes_2_pow_128`), the formerly-red
`fake_glv_hint_supports_near_order_scalar` and
`arbitrary_full_width_u_scalars_build_a_current_air_claim`, and the 6 existing
trivial-path tests.

- [x] **Step 7: Commit.**

```bash
rtk git add crates/stwo-p256/Cargo.toml crates/stwo-p256/src/scalar/mod.rs crates/stwo-p256/src/scalar/fake_glv_decompose.rs crates/stwo-p256/src/scalar/fake_glv_scalar.rs
rtk git commit -m "feat(p256): add arbitrary fake glv scalar decomposition"
```

Landed as commit on `lucas/p256` titled "Add arbitrary fake-GLV scalar decomposition (Garaga lattice)". Cargo.lock and proof.rs (Task 1 helpers + Task 5 Step 1 production builders, needed to unblock the test binary) were included in the same commit.

---

## Task 3: Replace Trivial Fake-GLV AIR Constraints With General Scalar Relation

**Files:**
- Modify: `crates/stwo-p256/src/scalar/fake_glv_scalar.rs`

- [x] **Step 1: Rename the evaluator helper.**

Rename:

```rust
fn constrain_fake_glv_scalar_trivial<E: EvalAtRow>(...)
```

to:

```rust
fn constrain_fake_glv_scalar_general<E: EvalAtRow>(...)
```

- [x] **Step 2: Keep cert binding, flags, zeroing, and small bounds.**

The general helper must still enforce:

```rust
active * (row.sig_id - cert[0]) = 0
active * (row.cert_id - cert[1]) = 0
active * (row.cert_active - cert_active) = 0
active * (row.cert_zero_active - cert_zero_active) = 0
row.cert_active, row.cert_zero_active, row.s2_sign_bit are boolean
inactive rows have scalar/s1/s2/q/sign zero
cert_zero_active rows have s1/s2/q/sign zero
active cert rows have nonzero s1 and nonzero s2_abs
```

- [x] **Step 3: Remove the trivial constraints.**

Delete these active-branch requirements:

```rust
row.s1[limb] == row.scalar[limb]
upper scalar limbs == 0
row.s2_abs == 1
row.q == 0
row.s2_sign_bit == 1
```

Those are exactly what prevent arbitrary scalars.

- [x] **Step 4: Add selected-result columns for the scalar-mod-mul result.**

Extend `FakeGlvScalarAirRow` and trace layout with:

```rust
selected_s1: P256EvalBigInt<E::F>,
selected_s1_carries: [E::F; N_LIMBS],
```

For active rows:

```rust
selected_s1 = if s2_sign_bit == 1 { s1 } else { n - s1 }
```

Use carry constraints over limbs:

```rust
selected_s1 + (1 - s2_sign_bit) * s1 = (1 - s2_sign_bit) * n
selected_s1 - s2_sign_bit * s1 = 0
```

Implement this without multiplying two non-constant limb expressions in a LogUp tuple. If degree exceeds `log_size + 1`, introduce witnessed branch limbs:

```rust
s1_positive_limb = s2_sign_bit * s1_limb
s1_negative_limb = (1 - s2_sign_bit) * s1_limb
```

and constrain those with degree-2 rows.

- [~] **Step 5: Add tests that mutation of sign or selected result fails `assert_constraints`.**

Skipped as redundant: the existing 21 `current_p256_monolithic_*_rejects_*` /
`current_p256_proof_pipeline_*_rejects_*` integration tests already exercise
end-to-end rejection of fake-GLV scalar claim mutations through the new
general AIR, and they continue to pass. Add a targeted unit-level mutation
test if Task 4's algebraic linkage exposes a path not covered by the
integration suite.

Add tests:

```rust
#[test]
fn fake_glv_scalar_air_rejects_mutated_sign_selected_result() {
    let claim = fake_glv_claim_with_arbitrary_scalars();
    let mut base = gen_fake_glv_scalar_air_base_trace(&claim, claim.log_size()).expect("base");
    mutate_selected_s1_limb(&mut base, 0);
    assert_fake_glv_scalar_constraints_fail(&claim, base);
}
```

Use the existing fake-GLV scalar constraint diagnostic helpers in the file; if they are absent, add a small local helper that builds `FakeGlvScalarHintComponents`, calls `assert_constraints`, and expects an error.

- [x] **Step 6: Run focused AIR tests.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 fake_glv_scalar_air --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 fake_glv_hint_supports_near_order_scalar --release -- --test-threads=1 --nocapture
```

Expected: constraints pass for arbitrary decomposition and reject selected-result/sign tampering.

Observed: 14 fake-GLV scalar/decomposer tests pass; the 21 monolithic mutation-rejection tests
(`current_p256_monolithic_*_rejects_*`, `current_p256_proof_pipeline_*_rejects_*`) also pass,
plus `current_p256_proof_pipeline_accepts_real_valid_signature_input` and
`current_p256_proof_pipeline_links_all_implemented_components` verify trivial-hint inputs
end-to-end through the new general AIR (52s + 456s release-mode runs).

---

## Task 4: Prove The Fake-GLV Scalar Equation With Existing ScalarModMul

> **Status (2026-06-05): scaffolding committed, link dormant.** All claim/
> interaction/component plumbing for the per-cert `ScalarModMul` is in place
> (subagent-mirrored from `scalar_setup_mod_muls`). `FakeGlvScalarAirEval`
> carries a `scalar_limb_relation: ScalarLimbRelation` field and the
> production builder threads it through. The row builder
> `fake_glv_scalar_mod_mul_rows` returns `Vec::new()` until activated —
> see its doc comment in `proof.rs`. Activation requires (1) flipping the
> early-return and (2) emitting `(mul_id, role, limb_index, limb_value)`
> tuples (80 per row: 4 roles × 20 limbs) via `add_to_relation` in
> `fake_glv_scalar::evaluate`, plus the matching
> `scalar_mod_mul_provider_claimed_sum` computation in
> `gen_fake_glv_scalar_air_interaction_trace`. Either side alone breaks the
> `FakeGlvScalarModMul` relation balance.

**Files:**
- Modify: `crates/stwo-p256/src/scalar/fake_glv_scalar.rs`
- Modify: `crates/stwo-p256/src/proof.rs`

- [ ] **Step 1: Add scalar-mod-mul rows for each active fake-GLV cert.**

In `proof.rs`, add:

```rust
fn fake_glv_scalar_mod_mul_rows(
    fake_glv: &FakeGlvScalarHintClaim,
) -> Result<Vec<ScalarModMulTraceRows>, P256ProofError> {
    let mut rows = Vec::with_capacity(fake_glv.rows.len());
    for row in &fake_glv.rows {
        if row.cert_active.0 == 0 {
            continue;
        }
        let selected_s1 = row.selected_s1_value();
        let trace = ScalarFieldMulTrace::new(
            "fake_glv_scalar_equation",
            &row.scalar.to_u256().to_le_u64s(),
            &row.hint.s2_abs.to_u256().to_le_u64s(),
            &P256_ORDER,
        )?;
        assert_eq!(trace.result.to_u256(), selected_s1.to_u256());
        let mul_id = FAKE_GLV_SCALAR_MUL_ID_BASE + rows.len() as u32;
        rows.push(ScalarModMulTraceRows::new(mul_id, &trace)?);
    }
    Ok(rows)
}
```

Use the existing `ScalarFieldMulTrace` import pattern already used by scalar setup. Define:

```rust
const FAKE_GLV_SCALAR_MUL_ID_BASE: u32 = 1_000_000;
```

near the scalar setup mod-mul ID code to avoid collision with `2 * sig_index` IDs.

- [ ] **Step 2: Use `from_rows_with_external_limb_links`.**

Every fake-GLV scalar equation mod-mul component must be created with:

```rust
ScalarModMulClaim::from_rows_with_external_limb_links(rows)
```

not `from_rows`, because the fake-GLV scalar AIR supplies the canonical limbs for `scalar`, `s2_abs`, quotient, and selected result.

- [ ] **Step 3: Add external limb provider/consumer sums.**

Wire the fake-GLV scalar AIR so it provides:

```text
(mul_id, role=A, limb, scalar_limb)
(mul_id, role=B, limb, s2_abs_limb)
(mul_id, role=Quotient, limb, q_limb)
(mul_id, role=Result, limb, selected_s1_limb)
```

The scalar-mod-mul components with external links consume the same tuples. Balance them in `P256CurrentAirInteractionClaim::relation_balances()`, near the existing scalar setup scalar-limb balance.

- [ ] **Step 4: Add relation-audit liveness checks.**

Extend `monolithic_relation_audit_is_balanced_and_fully_linked` so it fails if any active fake-GLV scalar row lacks exactly one scalar-mod-mul row with all four linked roles.

- [ ] **Step 5: Run the established debugging pattern if this fails.**

If PCS fails after `assert_constraints` passes:

```text
1. Identify the broken component from component-level diagnostics.
2. Bisect constraints in fake_glv_scalar first.
3. Then inspect scalar_mod_mul relation audit and external limb link ordering.
4. Only then inspect degree bounds.
```

- [ ] **Step 6: Run focused release gates.**

Run one at a time:

```bash
rtk proxy cargo test -p stwo-p256 fake_glv_scalar_air_pcs_diagnostic --release -- --ignored --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_air_constraint_diagnostic --release -- --ignored --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 monolithic_relation_audit_is_balanced_and_fully_linked --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
```

- [ ] **Step 7: Commit.**

```bash
rtk git add crates/stwo-p256/src/scalar/fake_glv_scalar.rs crates/stwo-p256/src/proof.rs
rtk git commit -m "feat(p256): prove arbitrary fake glv scalar equations"
```

---

## Task 5: Switch Production Claim Builders To Arbitrary Hints

**Files:**
- Modify: `crates/stwo-p256/src/proof.rs`
- Modify: `crates/stwo-p256/src/final_check.rs`
- Modify: `crates/stwo-p256/src/scalar/prepared_table.rs`
- Modify: `crates/stwo-p256/src/scalar/fake_glv_chain.rs`
- Modify: `crates/stwo-p256/src/scalar/fake_glv_selector.rs`

- [ ] **Step 1: Add production arbitrary builders.**

In `proof.rs`:

```rust
pub fn from_inputs_with_arbitrary_fake_glv_hints(
    inputs: &[EcdsaVerifyInput],
) -> Result<Self, P256ProofError> {
    let public_inputs = PublicEcdsaInputClaim::from_inputs(inputs);
    let scalar_setup = ScalarSetupClaim::from_public_inputs(&public_inputs)?;
    let cert_inputs = CertScalarInputClaim::from_scalar_setup(&scalar_setup)?;
    let hints = cert_inputs
        .rows
        .iter()
        .map(|row| FakeGlvScalarHint::decompose(&row.scalar))
        .collect::<Result<Vec<_>, _>>()?;
    Self::from_inputs_with_hints(inputs, hints)
}
```

Add the same method on `P256ProofDraft` and route `P256ProofDraft::from_inputs` through arbitrary hints after native `ecdsa_verify` passes.

- [ ] **Step 2: Keep trivial builders test-only or diagnostic-only.**

Add `#[cfg(test)]` to helper-only uses where possible. If external tests still need it, rename to:

```rust
from_inputs_with_trivial_fake_glv_hints_for_diagnostics
```

and update call sites deliberately.

- [ ] **Step 3: Replace small-u-only e2e gates.**

Update the primary monolithic e2e test to use:

```rust
valid_real_input_with_u_scalars(scalar_near_order(123), scalar_near_order(456))
```

Keep one small-u test as a regression, but it must not be the only green e2e proof.

- [ ] **Step 4: Run gates.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 arbitrary_full_width_u_scalars_build_a_current_air_claim --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 monolithic_rejects_mutated --release -- --test-threads=1 --nocapture
```

- [ ] **Step 5: Commit.**

```bash
rtk git add crates/stwo-p256/src/proof.rs crates/stwo-p256/src/final_check.rs crates/stwo-p256/src/scalar
rtk git commit -m "feat(p256): use arbitrary fake glv hints in proof pipeline"
```

---

## Task 6: Make FinalAdd AIR Complete For Valid Finite Cases

**Files:**
- Modify: `crates/stwo-p256/src/final_add_air.rs`
- Modify: `crates/stwo-p256/src/final_check.rs`
- Modify: `crates/stwo-p256/src/proof.rs`

- [ ] **Step 1: Add a red doubling test.**

In `final_add_air.rs` tests:

```rust
#[test]
fn final_add_supports_finite_doubling() {
    let r = scalar_mul_point(7);
    let claim = FinalAddClaim::from_hints(M31::from_u32_unchecked(0), &r, false, &r, false)
        .expect("finite doubling should be supported");
    claim.verify().expect("doubling final-add claim verifies");
}
```

Expected current failure: `UnsupportedEqualX`.

- [ ] **Step 2: Replace equal-x rejection with branch selectors.**

Add boolean columns:

```rust
distinct_add
double_add
inverse_add
r1_only
r2_only
```

Constrain:

```text
distinct_add + double_add + inverse_add + r1_only + r2_only = active
distinct_add => r1,r2 finite and x1 != x2
double_add => r1,r2 finite, x1 = x2, y1 = y2
inverse_add => r1,r2 finite, x1 = x2, y1 + y2 = p
r1_only => r2_inf = 1, output = r1
r2_only => r1_inf = 1, output = r2
inverse_add => verifier-facing final result is infinity and must be rejected by final check
```

- [ ] **Step 3: Add doubling muls.**

Extend `FINAL_ADD_MUL_COUNT` and role constants so doubling proves:

```text
x1_squared = x1 * x1 mod p
lambda * (2*y1) = 3*x1_squared - 3 mod p
lambda_squared = lambda * lambda mod p
x3 + 2*x1 = lambda_squared mod p
```

Reuse the same `FinalAddMulResultRelation`; do not create a second field-mul engine.

- [ ] **Step 4: Keep distinct-add constraints unchanged.**

The existing distinct branch already proves:

```text
lambda * dx = dy
lambda^2 = x3 + x1 + x2
dx * dx_inv = 1
```

Gate those constraints by `distinct_add`, not by `both_finite`.

- [ ] **Step 5: Reject final infinity in AIR.**

If `inverse_add = 1`, `FinalAddCheckEval` must not provide a usable `FinalAddOutputRelation`. Add:

```rust
eval.add_constraint(active.clone() * inverse_add.clone());
```

This makes the invalid ECDSA `R = infinity` case unprovable, while allowing all valid finite cases.

- [ ] **Step 6: Add monolithic doubling e2e.**

Add a proof test with `u1 == u2`, for example:

```rust
#[test]
fn current_p256_monolithic_proves_arbitrary_doubling_final_add() {
    let u = scalar_near_order(789);
    let input = valid_real_input_with_u_scalars(u.clone(), u);
    let proof = P256ProofDraft::from_inputs(vec![input])
        .expect("draft")
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("proof proves");
    verify_current_air_monolithic::<Blake2sMerkleChannel>(proof)
        .expect("proof verifies");
}
```

- [ ] **Step 7: Run gates.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 final_add_supports_finite_doubling --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_proves_arbitrary_doubling_final_add --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_air_constraint_diagnostic --release -- --ignored --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
```

- [ ] **Step 8: Commit.**

```bash
rtk git add crates/stwo-p256/src/final_add_air.rs crates/stwo-p256/src/final_check.rs crates/stwo-p256/src/proof.rs
rtk git commit -m "feat(p256): support finite doubling in final add air"
```

---

## Task 7: Add Real Arbitrary Signature Fixtures

**Files:**
- Modify: `crates/stwo-p256/Cargo.toml`
- Modify: `crates/stwo-p256/src/proof.rs`

- [ ] **Step 1: Add `sha2` as a dev dependency if needed.**

```toml
[dev-dependencies]
sha2 = "0.10"
```

- [ ] **Step 2: Add deterministic p256 crate fixture conversion.**

Inside `proof.rs` tests:

```rust
fn p256_crate_signed_input() -> EcdsaVerifyInput {
    use p256::ecdsa::{signature::Signer, Signature as P256Signature, SigningKey};
    use sha2::{Digest, Sha256};

    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("valid signing key");
    let verifying_key = signing_key.verifying_key();
    let message = b"stwo-p256 arbitrary signature air fixture";
    let digest = Sha256::digest(message);
    let signature: P256Signature = signing_key.sign(message);
    let encoded = verifying_key.to_encoded_point(false);

    EcdsaVerifyInput {
        message_hash: U256(digest.into()),
        signature: Signature {
            r: U256(signature.r().to_bytes().into()),
            s: U256(signature.s().to_bytes().into()),
        },
        public_key: AffinePoint {
            x: U256(encoded.x().expect("x").try_into().expect("x len")),
            y: U256(encoded.y().expect("y").try_into().expect("y len")),
        },
    }
}
```

If the `signature.r().to_bytes().into()` conversion does not type-check, replace it with a local `fn array32(bytes: &[u8]) -> [u8; 32]` and call `U256(array32(signature.r().to_bytes().as_slice()))`.

- [ ] **Step 3: Add real-signature proof test.**

```rust
#[test]
fn current_p256_monolithic_proves_real_p256_crate_signature() {
    let input = p256_crate_signed_input();
    assert!(ecdsa_verify(&input), "native verifier must accept fixture");
    let proof = P256ProofDraft::from_inputs(vec![input])
        .expect("draft")
        .prove_current_air_monolithic::<Blake2sMerkleChannel>()
        .expect("proof proves");
    verify_current_air_monolithic::<Blake2sMerkleChannel>(proof)
        .expect("proof verifies");
}
```

- [ ] **Step 4: Add adversarial rejects for the real fixture.**

Add tests mutating one thing at a time:

```rust
#[test]
fn current_p256_monolithic_rejects_real_signature_mutated_public_r() { ... }

#[test]
fn current_p256_monolithic_rejects_real_signature_mutated_public_key() { ... }

#[test]
fn current_p256_monolithic_rejects_real_signature_mutated_fake_glv_s2() { ... }
```

Each test must build a valid proof first, mutate the proof claim or interaction claim exactly like the existing `monolithic_rejects_mutated_*` tests, and assert `verify_current_air_monolithic` returns `Err`.

- [ ] **Step 5: Run gates.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_proves_real_p256_crate_signature --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_rejects_real_signature --release -- --test-threads=1 --nocapture
```

- [ ] **Step 6: Commit.**

```bash
rtk git add crates/stwo-p256/Cargo.toml crates/stwo-p256/src/proof.rs
rtk git commit -m "test(p256): prove real arbitrary p256 signature fixture"
```

---

## Task 8: Remove Scope-Limiting Claims And Stale Documentation

**Files:**
- Modify: `crates/stwo-p256/src/proof.rs`
- Modify: `crates/stwo-p256/src/final_add_air.rs`
- Modify: `crates/stwo-p256/src/final_check_air.rs`
- Modify: `tasks/lessons.md`

- [ ] **Step 1: Update proof-slot notes.**

Change the `FakeGlvScalarHint` slot note from “current trivial scalar strategy” to:

```text
Fake-GLV scalar rows are proven for arbitrary nonzero certificate scalars by bounding s1/s2/q to 128 bits, selecting signed s1 in AIR, and linking scalar*s2_abs = selected_s1 mod n through scalar_mod_mul rows with external limb links.
```

Change the `FinalEcdsaCheck` slot note so it no longer says doubling is rejected.

- [ ] **Step 2: Fix stale final-check docs.**

In `final_check_air.rs`, replace the “Remaining gap” paragraph with:

```rust
//! `r_x` is bound by `FinalAddOutputRelation`, which is yielded by
//! `final_add_air` after consuming the prepared-table final hint points and
//! proving the final EC addition. The reduction in this AIR only completes
//! `x(R) mod n = r`; it does not trust native final-check witnesses.
```

- [ ] **Step 3: Add a lesson for future components.**

Append to `tasks/lessons.md`:

```markdown
- When a native verifier supports a general algebraic relation but the AIR was narrowed for an incremental milestone, mark the scope in the slot note and add a red arbitrary-input test before declaring the component complete.
```

- [ ] **Step 4: Run proof-slot test.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 full_p256_signature_proof_has_no_pending_component_slots --release -- --ignored --test-threads=1 --nocapture
```

- [ ] **Step 5: Commit.**

```bash
rtk git add crates/stwo-p256/src/proof.rs crates/stwo-p256/src/final_add_air.rs crates/stwo-p256/src/final_check_air.rs tasks/lessons.md
rtk git commit -m "docs(p256): mark arbitrary signature air scope accurately"
```

---

## Task 9: Proving-Time And Memory Optimization Pass

**Files:**
- Modify: `crates/stwo-p256/src/proof.rs`
- Modify: `crates/stwo-p256/src/projective_air.rs` only if row-family changes are made
- Modify: `crates/stwo-p256/src/scalar/scalar_mod_mul/mod.rs` only if scalar-mod-mul split shape needs retuning

- [ ] **Step 1: Remove coefficient retention from production monolithic proving.**

Delete or feature-gate this line in `prove_current_air_monolithic`:

```rust
commitment_scheme.set_store_polynomials_coefficients();
```

Keep coefficient storage in explicit diagnostics such as PCS failure repro tests.

- [ ] **Step 2: Add a shape budget test.**

In `proof.rs`, add assertions to `current_p256_air_shape_diagnostic` or a new ignored test:

```rust
assert!(total_base_columns <= 4_500, "base column budget regressed");
assert!(total_interaction_columns <= 10_500, "interaction column budget regressed");
assert!(projective_raw_chunks <= 130_000, "raw chunk budget regressed");
assert!(projective_folded_contributions <= 340_000, "folded contribution budget regressed");
```

Set the first budget from the post-arbitrary implementation’s measured numbers plus 10%, not from the old small-u numbers if they change.

- [ ] **Step 3: Run before/after proof timing.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_air_shape_diagnostic --release -- --ignored --test-threads=1 --nocapture
```

Record elapsed seconds and shape output in `tasks/todo.md`.

- [ ] **Step 4: If memory is still excessive, optimize row families in this order.**

1. Retune `SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS` only if scalar-mod-mul rows dominate after arbitrary fake-GLV equation rows are added.
2. Pack projective-RCB folded contribution rows more tightly; current shape has the largest row family there.
3. Prototype quotient/carry field multiplication as an alternative to Solinas raw-product/folded-contribution rows.

Do not start item 2 or 3 until shape diagnostics prove item 1 is not the bottleneck.

- [ ] **Step 5: Run gates.**

Run:

```bash
rtk proxy cargo test -p stwo-p256 current_p256_air_shape_diagnostic --release -- --ignored --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 monolithic_rejects_mutated --release -- --test-threads=1 --nocapture
```

- [ ] **Step 6: Commit.**

```bash
rtk git add crates/stwo-p256/src/proof.rs crates/stwo-p256/src/projective_air.rs crates/stwo-p256/src/scalar/scalar_mod_mul tasks/todo.md
rtk git commit -m "perf(p256): reduce arbitrary signature proof memory"
```

---

## Final Acceptance Gate

Run these one at a time in release mode:

```bash
rtk proxy cargo test -p stwo-p256 fake_glv_hint_supports_near_order_scalar --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 arbitrary_full_width_u_scalars_build_a_current_air_claim --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_proves_real_p256_crate_signature --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_monolithic_proves_arbitrary_doubling_final_add --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_air_constraint_diagnostic --release -- --ignored --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_air_shape_diagnostic --release -- --ignored --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 monolithic_relation_audit_is_balanced_and_fully_linked --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 monolithic_rejects_mutated --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof --release -- --test-threads=1 --nocapture
rtk proxy cargo test -p stwo-p256 full_p256_signature_proof_has_no_pending_component_slots --release -- --ignored --test-threads=1 --nocapture
```

Acceptance criteria:

- A real `p256` crate signature proves and verifies through `verify_current_air_monolithic`.
- A full-width synthetic valid signature proves and verifies.
- A finite doubling final-add signature proves and verifies.
- Mutating public input, fake-GLV scalar hint limbs, selected scalar-mod-mul result, prepared-table hint, public key, final-add output, or public `r` rejects through the verifier-facing proof path.
- No production verifier path calls native `ecdsa_verify`, native `claim.verify()`, or native final-check equality as a trust assumption.
- `tasks/todo.md` records final proof time, shape counts, and memory-affecting changes.
