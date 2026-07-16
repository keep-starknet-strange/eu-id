# Credible Mdoc Proof Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the synthetic `EUID` proof path with a credible mdoc-backed proof path where predicates are proven over issuer-signed mdoc attribute items, with nonce/session binding preserved.

**Architecture:** Keep the expensive primitives that already work: SHA-256, P-256 ECDSA, age, nationality, and `air-core` single-proof orchestration. Add a real mdoc binding layer around them: host-side mdoc/COSE validation prepares public digest slots and private item witnesses, while new AIR glue proves `SHA-256(IssuerSignedItemBytes)` equals those digest slots and parses the predicate values from the hashed item bytes. Defer full in-circuit X.509 and general CBOR parsing until the digest-slot and item-value binding path is green.

**Tech Stack:** Rust 2021, Stwo AIR components, `air-core` module orchestration, existing `stwo-sha256`, existing `stwo-p256`, existing `predicates`, `ciborium` for deterministic CBOR/fixtures, `sha2`/`p256` host references, Cargo release integration tests.

---

## Scope Summary

This is not just proving things already provable. The existing SHA/P256/predicate circuits remain useful, but a credible mdoc project needs new binding circuits and new host validation.

Reuse existing circuits:
- SHA-256 proving for item bytes and COSE/Sig_structure bytes.
- P-256 ECDSA proof for issuer signature when the signed bytes are represented as a SHA digest.
- Predicate AIRs for age and nationality.
- `air-core` one-proof orchestration and global LogUp balance.
- Existing digest byte bridge pattern.

New circuit work:
- Bind multiple SHA instances by role: birth-date item digest, nationality item digest, optional issuer-auth digest.
- Prove digest equality against the correct mdoc `valueDigests` slot.
- Parse DOB and nationality from private `IssuerSignedItemBytes`, or from a strict supported encoding subset, inside AIR.
- Generalize byte exposure beyond hardcoded first-block `EUID` offsets.
- Bind statement/session data into the proof transcript or keep a formally specified envelope boundary with tests.

Host/protocol work:
- Validate real mdoc/COSE structure and issuer trust externally for the first credible milestone.
- Prepare witness data with explicit digest IDs, namespaces, element IDs, item bytes, parsed offsets, and public digest slots.
- Update SDK contracts so currently unused fields (`mso`, `IssuerSignedItemBytes`, `sig_structure`, issuer signature) become live.

## Milestone Boundaries

### Milestone 1: Credible Practical Mdoc Proof

Verifier or SDK validates mdoc/COSE/trust chain outside the STARK, then the STARK proves:

```text
SHA-256(private birth_date IssuerSignedItemBytes) == public MSO digest slot
SHA-256(private nationality IssuerSignedItemBytes) == public MSO digest slot
private birth_date item parses to DOB used by age predicate
private nationality item parses to nationality code used by nat predicate
issuer key / policy / doctype / namespace / element IDs / nonce are bound by statement bytes
```

This is credible because predicates are over issuer-signed item bytes. It does not claim in-circuit certificate validation.

### Milestone 2: Stronger Issuer Auth Binding

Also prove:

```text
SHA-256(private COSE Sig_structure) == ECDSA z
P-256 verifies issuer signature over that z
public MSO digest slots are inside the signed MSO payload
```

This reuses SHA/P256 but adds substantial COSE/MSO structure binding.

### Milestone 3: Full In-Circuit Mdoc Structure

Prove enough CBOR/COSE/MSO structure in-circuit to avoid trusting host extraction for digest slots and item structure. X.509 chain validation can remain external with the trusted issuer/cert hash bound publicly, unless the project explicitly targets full certificate-chain proof.

---

## File Structure

Planned new files:

- `crates/eu-id-prover/src/mdoc/mod.rs`  
  Mdoc proof API types and module assembly.

- `crates/eu-id-prover/src/mdoc/statement.rs`  
  Public statement model for mdoc proof: issuer key or issuer cert hash, doctype, namespace, element IDs, policy, digest slots, nonce/session hash, circuit version.

- `crates/eu-id-prover/src/mdoc/witness.rs`  
  Private mdoc witness: item bytes, parsed item layout witnesses, optional Sig_structure bytes, issuer signature.

- `crates/eu-id-prover/src/mdoc/item_digest_bind.rs`  
  AIR module that consumes SHA digest bytes and binds them to public mdoc value-digest slots.

- `crates/eu-id-prover/src/mdoc/item_value_bind.rs`  
  AIR module that proves selected item bytes parse to predicate values.

- `crates/eu-id-prover/tests/mdoc_credible_flow.rs`  
  End-to-end mdoc-backed positive and negative tests.

- `crates/eu-id-prover/tests/fixtures/mdoc/`  
  Deterministic fixture bytes for supported mdoc-shaped items and MSO digest slots.

- `crates/sdk/src/mdoc_contract.rs`  
  SDK mapping from existing `ZkPublicStatement` / `ZkWitness` into the new mdoc proof API.

Planned modified files:

- `Cargo.toml`  
  Add any internal crate/module dependencies if needed.

- `crates/eu-id-prover/src/lib.rs`  
  Re-export mdoc proof API without disrupting the existing synthetic proof API.

- `crates/stwo-sha256/src/field_exposure.rs`  
  Generalize exposure spec from fixed first-block windows to role-keyed dynamic windows where needed.

- `crates/stwo-sha256/src/air.rs`, `crates/stwo-sha256/src/interaction.rs`, `crates/stwo-sha256/src/trace.rs`  
  Carry generalized exposure metadata through trace, AIR, and interaction paths.

- `crates/sdk/src/lib.rs`, `crates/sdk/src/mapping.rs`  
  Stop ignoring live mdoc witness fields on the mdoc proof path.

- `tasks/todo.md`  
  Track execution status for this plan.

---

## Task 1: Add Mdoc Proof Types Without Changing Existing Proof Behavior

**Files:**
- Create: `crates/eu-id-prover/src/mdoc/mod.rs`
- Create: `crates/eu-id-prover/src/mdoc/statement.rs`
- Create: `crates/eu-id-prover/src/mdoc/witness.rs`
- Modify: `crates/eu-id-prover/src/lib.rs`
- Test: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Write the API shape test**

Add `crates/eu-id-prover/tests/mdoc_credible_flow.rs`:

```rust
use eu_id_prover::mdoc::{
    MdocElementId, MdocNamespace, MdocProofStatement, MdocWitness, SessionBinding,
};

#[test]
fn mdoc_statement_carries_credential_context_and_policy() {
    let statement = MdocProofStatement::new_for_pid_demo(
        SessionBinding::from_nonce(vec![0xab, 0xcd, 0xef]),
        18,
        vec![276, 250],
    );

    assert_eq!(statement.doctype.as_str(), "eu.europa.ec.eudi.pid.1");
    assert_eq!(statement.birth_date_element, MdocElementId::new("birth_date"));
    assert_eq!(statement.nationality_element, MdocElementId::new("nationality"));
    assert_eq!(
        statement.namespace,
        MdocNamespace::new("eu.europa.ec.eudi.pid.1")
    );
    assert_eq!(statement.policy.min_age_years, 18);
    assert_eq!(statement.policy.accepted_nationalities, vec![276, 250]);
    assert_eq!(statement.session.statement_hash().len(), 32);
}

#[test]
fn mdoc_witness_requires_item_bytes_for_active_predicates() {
    let statement = MdocProofStatement::new_for_pid_demo(
        SessionBinding::from_nonce(vec![1, 2, 3, 4]),
        18,
        vec![276, 250],
    );
    let witness = MdocWitness::empty();

    let err = witness.validate_for(&statement).expect_err("empty witness rejects");
    assert!(
        err.to_string().contains("birth_date item bytes are missing"),
        "unexpected error: {err}"
    );
}
```

- [ ] **Step 2: Run the test and confirm it fails on missing module**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow mdoc_statement_carries_credential_context_and_policy
```

Expected: compile failure naming missing `eu_id_prover::mdoc`.

- [ ] **Step 3: Add the module skeleton**

Add `crates/eu-id-prover/src/mdoc/mod.rs`:

```rust
//! Mdoc-backed proof API.
//!
//! This module is the credibility upgrade path from the synthetic `EUID`
//! credential. It keeps host mdoc/COSE validation outside the STARK for the
//! first milestone, while the STARK binds private item bytes to public digest
//! slots and parses predicate values from those item bytes.

pub mod statement;
pub mod witness;

pub use statement::{MdocElementId, MdocNamespace, MdocProofStatement, SessionBinding};
pub use witness::{MdocWitness, MdocWitnessError};
```

Add `crates/eu-id-prover/src/mdoc/statement.rs`:

```rust
use sha2::{Digest, Sha256};

use crate::{Date, Policy};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocNamespace(String);

impl MdocNamespace {
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocElementId(String);

impl MdocElementId {
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SessionBinding {
    nonce: Vec<u8>,
}

impl SessionBinding {
    pub fn from_nonce(nonce: Vec<u8>) -> Self {
        Self { nonce }
    }

    pub fn statement_hash(&self) -> [u8; 32] {
        Sha256::digest(&self.nonce).into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocProofStatement {
    pub doctype: String,
    pub namespace: MdocNamespace,
    pub birth_date_element: MdocElementId,
    pub nationality_element: MdocElementId,
    pub session: SessionBinding,
    pub policy: Policy,
}

impl MdocProofStatement {
    pub fn new_for_pid_demo(
        session: SessionBinding,
        min_age_years: u32,
        accepted_nationalities: Vec<u32>,
    ) -> Self {
        Self {
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: MdocNamespace::new("eu.europa.ec.eudi.pid.1"),
            birth_date_element: MdocElementId::new("birth_date"),
            nationality_element: MdocElementId::new("nationality"),
            session,
            policy: Policy {
                current_date: Date {
                    year: 2026,
                    month: 7,
                    day: 3,
                },
                min_age_years,
                accepted_nationalities,
            },
        }
    }
}
```

Add `crates/eu-id-prover/src/mdoc/witness.rs`:

```rust
use core::fmt;

use super::MdocProofStatement;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MdocWitness {
    pub birth_date_item_bytes: Vec<u8>,
    pub nationality_item_bytes: Vec<u8>,
}

impl MdocWitness {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn validate_for(&self, _statement: &MdocProofStatement) -> Result<(), MdocWitnessError> {
        if self.birth_date_item_bytes.is_empty() {
            return Err(MdocWitnessError::MissingBirthDateItem);
        }
        if self.nationality_item_bytes.is_empty() {
            return Err(MdocWitnessError::MissingNationalityItem);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocWitnessError {
    MissingBirthDateItem,
    MissingNationalityItem,
}

impl fmt::Display for MdocWitnessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingBirthDateItem => write!(f, "birth_date item bytes are missing"),
            Self::MissingNationalityItem => write!(f, "nationality item bytes are missing"),
        }
    }
}

impl std::error::Error for MdocWitnessError {}
```

Modify `crates/eu-id-prover/src/lib.rs`:

```rust
pub mod mdoc;
```

- [ ] **Step 4: Run the API test**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow mdoc_statement_carries_credential_context_and_policy
```

Expected: test passes.

- [ ] **Step 5: Run all new mdoc API tests**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow
```

Expected: 2 tests pass.

- [ ] **Step 6: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/src/lib.rs crates/eu-id-prover/src/mdoc crates/eu-id-prover/tests/mdoc_credible_flow.rs
rtk git commit -m "feat(eu-id-prover): add mdoc proof API skeleton"
```

Expected: commit succeeds.

---

## Task 2: Add Deterministic Mdoc Item Fixtures

**Files:**
- Create: `crates/eu-id-prover/tests/fixtures/mdoc/mod.rs`
- Create: `crates/eu-id-prover/tests/fixtures/mdoc/pid_items.rs`
- Modify: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Add fixture tests for item bytes and digests**

Append to `crates/eu-id-prover/tests/mdoc_credible_flow.rs`:

```rust
mod fixtures;

#[test]
fn mdoc_item_fixtures_have_stable_sha256_digests() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();

    assert_eq!(fixture.birth_date_value, "1990-07-15");
    assert_eq!(fixture.nationality_alpha2, "DE");
    assert_eq!(
        hex::encode(fixture.birth_date_digest),
        hex::encode(sha2::Sha256::digest(&fixture.birth_date_item_bytes)),
    );
    assert_eq!(
        hex::encode(fixture.nationality_digest),
        hex::encode(sha2::Sha256::digest(&fixture.nationality_item_bytes)),
    );
}
```

- [ ] **Step 2: Add test fixture module**

Create `crates/eu-id-prover/tests/fixtures/mod.rs`:

```rust
pub mod mdoc;
```

Create `crates/eu-id-prover/tests/fixtures/mdoc/mod.rs`:

```rust
pub mod pid_items;
```

Create `crates/eu-id-prover/tests/fixtures/mdoc/pid_items.rs`:

```rust
use sha2::{Digest, Sha256};

#[derive(Clone, Debug)]
pub struct PidItemFixture {
    pub birth_date_item_bytes: Vec<u8>,
    pub nationality_item_bytes: Vec<u8>,
    pub birth_date_value: &'static str,
    pub nationality_alpha2: &'static str,
    pub birth_date_digest: [u8; 32],
    pub nationality_digest: [u8; 32],
}

pub fn valid_pid_items() -> PidItemFixture {
    // Strict fixture encoding used for the first circuit milestone:
    // EUID-MDOC-ITEM\0<element-id>\0<utf8-value>
    // This is not a complete mdoc item parser; it is a deterministic test
    // source for the circuit binding before real parser integration lands.
    let birth_date_item_bytes = b"EUID-MDOC-ITEM\0birth_date\01990-07-15".to_vec();
    let nationality_item_bytes = b"EUID-MDOC-ITEM\0nationality\0DE".to_vec();
    PidItemFixture {
        birth_date_digest: Sha256::digest(&birth_date_item_bytes).into(),
        nationality_digest: Sha256::digest(&nationality_item_bytes).into(),
        birth_date_item_bytes,
        nationality_item_bytes,
        birth_date_value: "1990-07-15",
        nationality_alpha2: "DE",
    }
}
```

- [ ] **Step 3: Add `hex` as a dev dependency if absent**

Check:

```bash
rtk grep "hex =" Cargo.toml crates/eu-id-prover/Cargo.toml
```

If absent, modify `crates/eu-id-prover/Cargo.toml`:

```toml
[dev-dependencies]
hex = "0.4"
```

If `[dev-dependencies]` already exists, add only:

```toml
hex = "0.4"
```

- [ ] **Step 4: Run fixture test**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow mdoc_item_fixtures_have_stable_sha256_digests
```

Expected: test passes.

- [ ] **Step 5: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/Cargo.toml crates/eu-id-prover/tests
rtk git commit -m "test(eu-id-prover): add deterministic mdoc item fixtures"
```

Expected: commit succeeds.

---

## Task 3: Generalize SHA Field Exposure to Role-Keyed Windows

**Files:**
- Modify: `crates/stwo-sha256/src/field_exposure.rs`
- Modify: `crates/stwo-sha256/src/trace.rs`
- Modify: `crates/stwo-sha256/src/interaction.rs`
- Modify: `crates/stwo-sha256/src/air.rs`
- Test: existing `stwo-sha256` unit tests plus new tests in `field_exposure.rs`

- [ ] **Step 1: Write tests for multi-role field exposure**

Add tests to `crates/stwo-sha256/src/field_exposure.rs`:

```rust
#[test]
fn role_keyed_windows_can_expose_item_values_after_byte_zero() {
    let exposure = FieldExposure::from_preimage_windows(&[
        (10, 15, 10), // birth date value in strict fixture
        (11, 17, 2),  // nationality value in strict fixture
    ]);

    assert_eq!(exposure.n_yields(), 12);
    assert_eq!(exposure.yields()[0].field_id, 10);
    assert_eq!(exposure.yields()[0].byte_index, 0);
    assert_eq!(exposure.yields()[10].field_id, 11);
    assert_eq!(exposure.yields()[10].byte_index, 0);
}

#[test]
fn exposure_rejects_windows_that_cross_supported_preimage_limit() {
    let result = std::panic::catch_unwind(|| {
        FieldExposure::from_preimage_windows(&[(10, 63, 2)]);
    });
    assert!(result.is_err(), "first milestone exposure is single-block only");
}
```

- [ ] **Step 2: Run the field exposure tests**

Run:

```bash
rtk cargo test -p stwo-sha256 field_exposure
```

Expected: tests pass if current first-block generalized role tags are enough. If this fails because the existing implementation assumes only `DOB` and `NATIONALITY`, remove that assumption and keep the single-block limit.

- [ ] **Step 3: Introduce named role constants for mdoc fields**

Modify `crates/air-core/src/relations.rs` in `field_id`:

```rust
pub const MDOC_BIRTH_DATE_VALUE: u32 = 10;
pub const MDOC_NATIONALITY_VALUE: u32 = 11;
```

- [ ] **Step 4: Add collision test for field IDs**

Add to `crates/air-core/src/relations.rs` tests:

```rust
#[test]
fn mdoc_field_ids_do_not_collide_with_synthetic_ids() {
    let ids = [
        field_id::DOB,
        field_id::NATIONALITY,
        field_id::MDOC_BIRTH_DATE_VALUE,
        field_id::MDOC_NATIONALITY_VALUE,
    ];
    for i in 0..ids.len() {
        for j in i + 1..ids.len() {
            assert_ne!(ids[i], ids[j], "field id collision at {i}/{j}");
        }
    }
}
```

- [ ] **Step 5: Run relation and SHA tests**

Run:

```bash
rtk cargo test -p air-core field_ids
rtk cargo test -p stwo-sha256 field_exposure
```

Expected: all tests pass.

- [ ] **Step 6: Commit**

Run:

```bash
rtk git add crates/air-core/src/relations.rs crates/stwo-sha256/src
rtk git commit -m "feat(sha256): add mdoc field exposure roles"
```

Expected: commit succeeds.

---

## Task 4: Add Item Digest Binding Module

**Files:**
- Create: `crates/eu-id-prover/src/mdoc/item_digest_bind.rs`
- Modify: `crates/eu-id-prover/src/mdoc/mod.rs`
- Modify: `crates/eu-id-prover/src/mdoc/statement.rs`
- Test: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Write unit test for public digest slot binding data**

Append to `crates/eu-id-prover/tests/mdoc_credible_flow.rs`:

```rust
use eu_id_prover::mdoc::{MdocDigestSlot, MdocDigestSlotSet};

#[test]
fn digest_slots_are_keyed_by_namespace_element_and_digest_id() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let slots = MdocDigestSlotSet::new(vec![
        MdocDigestSlot::new(
            "eu.europa.ec.eudi.pid.1",
            "birth_date",
            7,
            fixture.birth_date_digest,
        ),
        MdocDigestSlot::new(
            "eu.europa.ec.eudi.pid.1",
            "nationality",
            9,
            fixture.nationality_digest,
        ),
    ])
    .expect("distinct slots");

    assert_eq!(
        slots
            .find("eu.europa.ec.eudi.pid.1", "birth_date", 7)
            .expect("birth date slot")
            .digest,
        fixture.birth_date_digest
    );
    assert!(slots.find("wrong", "birth_date", 7).is_none());
}
```

- [ ] **Step 2: Add digest slot public types**

Modify `crates/eu-id-prover/src/mdoc/statement.rs`:

```rust
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocDigestSlot {
    pub namespace: String,
    pub element_id: String,
    pub digest_id: u32,
    pub digest: [u8; 32],
}

impl MdocDigestSlot {
    pub fn new(
        namespace: impl Into<String>,
        element_id: impl Into<String>,
        digest_id: u32,
        digest: [u8; 32],
    ) -> Self {
        Self {
            namespace: namespace.into(),
            element_id: element_id.into(),
            digest_id,
            digest,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MdocDigestSlotSet {
    slots: Vec<MdocDigestSlot>,
}

impl MdocDigestSlotSet {
    pub fn new(slots: Vec<MdocDigestSlot>) -> Result<Self, MdocDigestSlotError> {
        let mut keys = HashSet::new();
        for slot in &slots {
            let key = (&slot.namespace, &slot.element_id, slot.digest_id);
            if !keys.insert(key) {
                return Err(MdocDigestSlotError::DuplicateSlot);
            }
        }
        Ok(Self { slots })
    }

    pub fn find(&self, namespace: &str, element_id: &str, digest_id: u32) -> Option<&MdocDigestSlot> {
        self.slots.iter().find(|slot| {
            slot.namespace == namespace
                && slot.element_id == element_id
                && slot.digest_id == digest_id
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MdocDigestSlotError {
    DuplicateSlot,
}
```

Modify exports in `crates/eu-id-prover/src/mdoc/mod.rs`:

```rust
pub use statement::{
    MdocDigestSlot, MdocDigestSlotError, MdocDigestSlotSet, MdocElementId, MdocNamespace,
    MdocProofStatement, SessionBinding,
};
```

- [ ] **Step 3: Run digest slot test**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow digest_slots_are_keyed_by_namespace_element_and_digest_id
```

Expected: test passes.

- [ ] **Step 4: Add AIR module design skeleton**

Create `crates/eu-id-prover/src/mdoc/item_digest_bind.rs`:

```rust
//! Mdoc item digest binding.
//!
//! The SHA module yields `SHA-256(IssuerSignedItemBytes)` as 32 digest bytes.
//! This module consumes those digest bytes and binds them to public mdoc digest
//! slots keyed by `(namespace, element_id, digest_id)`.
//!
//! The first implementation should mirror `DigestBindProver` structurally but
//! consume only the SHA digest relation and compare against public slot bytes.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemDigestBindRow {
    pub item_id: u32,
    pub digest_id: u32,
    pub digest: [u8; 32],
}
```

Export it in `crates/eu-id-prover/src/mdoc/mod.rs`:

```rust
pub mod item_digest_bind;
```

- [ ] **Step 5: Commit skeleton and public slot model**

Run:

```bash
rtk git add crates/eu-id-prover/src/mdoc crates/eu-id-prover/tests/mdoc_credible_flow.rs
rtk git commit -m "feat(eu-id-prover): model mdoc digest slots"
```

Expected: commit succeeds.

---

## Task 5: Prove Item Digest Equality Against Public Slots

**Files:**
- Modify: `crates/eu-id-prover/src/mdoc/item_digest_bind.rs`
- Modify: `crates/eu-id-prover/src/mdoc/mod.rs`
- Test: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Write digest mismatch rejection test at relation level**

Append to `crates/eu-id-prover/tests/mdoc_credible_flow.rs`:

```rust
use eu_id_prover::mdoc::item_digest_bind::{
    item_digest_claimed_sum, ItemDigestBindRow, ItemDigestRelation,
};
use stwo::core::channel::{Blake2sChannel, Channel};

#[test]
fn item_digest_relation_balances_only_for_matching_digest() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let mut channel = Blake2sChannel::default();
    let relation = ItemDigestRelation::draw(&mut channel);

    let public_row = ItemDigestBindRow {
        item_id: 1,
        digest_id: 7,
        digest: fixture.birth_date_digest,
    };
    let mut private_row = public_row.clone();

    let public_sum = item_digest_claimed_sum(&[public_row.clone()], &relation, -1);
    let private_sum = item_digest_claimed_sum(&[private_row.clone()], &relation, 1);
    assert_eq!(public_sum + private_sum, stwo::core::fields::qm31::SecureField::zero());

    private_row.digest[0] ^= 1;
    let bad_private_sum = item_digest_claimed_sum(&[private_row], &relation, 1);
    assert_ne!(public_sum + bad_private_sum, stwo::core::fields::qm31::SecureField::zero());
}
```

- [ ] **Step 2: Implement relation helper**

Modify `crates/eu-id-prover/src/mdoc/item_digest_bind.rs`:

```rust
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::{relation, Relation};

pub const ITEM_DIGEST_RELATION_ARITY: usize = 2 + 32;

relation!(ItemDigestRelation, ITEM_DIGEST_RELATION_ARITY);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemDigestBindRow {
    pub item_id: u32,
    pub digest_id: u32,
    pub digest: [u8; 32],
}

pub fn item_digest_values(row: &ItemDigestBindRow) -> [M31; ITEM_DIGEST_RELATION_ARITY] {
    let mut values = [M31::from_u32_unchecked(0); ITEM_DIGEST_RELATION_ARITY];
    values[0] = M31::from_u32_unchecked(row.item_id);
    values[1] = M31::from_u32_unchecked(row.digest_id);
    for (idx, byte) in row.digest.iter().enumerate() {
        values[2 + idx] = M31::from_u32_unchecked(u32::from(*byte));
    }
    values
}

pub fn item_digest_claimed_sum(
    rows: &[ItemDigestBindRow],
    relation: &ItemDigestRelation,
    multiplicity: i32,
) -> SecureField {
    rows.iter()
        .map(|row| {
            let values = item_digest_values(row);
            SecureField::from(M31::from_u32_unchecked(multiplicity.unsigned_abs()))
                * if multiplicity < 0 {
                    -SecureField::one()
                } else {
                    SecureField::one()
                }
                / relation.combine(&values)
        })
        .sum()
}
```

- [ ] **Step 3: Run relation test**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow item_digest_relation_balances_only_for_matching_digest
```

Expected: test passes.

- [ ] **Step 4: Replace helper-only implementation with real `Air` module**

Implement `ItemDigestBindProver` and `ItemDigestBindVerifier` following the patterns in:

- `crates/stwo-p256/src/components/digest_bind/module.rs`
- `crates/air-core/src/lib.rs`

The component must:

- mix public rows into the transcript;
- draw one `ItemDigestRelation`;
- provide public digest rows with multiplicity `-1`;
- consume SHA-provided digest rows with multiplicity `+1`;
- return claimed sums so `air_core::verify` rejects mismatch through global balance;
- use explicit `item_id` and `digest_id` keys to prevent birth-date/nationality digest swaps.

- [ ] **Step 5: Add focused positive and negative proof tests**

Add tests:

```rust
#[test]
#[ignore = "slow: runs SHA plus item digest binding through air-core"]
fn item_digest_binding_accepts_matching_sha_item_digest() {
    // Build SHA witness over fixture.birth_date_item_bytes.
    // Build public digest row from fixture.birth_date_digest.
    // Prove SHA + item_digest_bind.
    // Verify succeeds.
}

#[test]
#[ignore = "slow: runs SHA plus item digest binding through air-core"]
fn item_digest_binding_rejects_swapped_digest_slot() {
    // Build SHA witness over fixture.birth_date_item_bytes.
    // Build public digest row from fixture.nationality_digest under birth_date key.
    // Prove may produce a proof, but verify rejects through global balance.
}
```

- [ ] **Step 6: Run focused ignored tests**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow item_digest_binding --release -- --ignored
```

Expected: matching digest accepts; swapped digest rejects.

- [ ] **Step 7: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/src/mdoc/item_digest_bind.rs crates/eu-id-prover/tests/mdoc_credible_flow.rs
rtk git commit -m "feat(eu-id-prover): prove mdoc item digest binding"
```

Expected: commit succeeds.

---

## Task 6: Add Strict Item Value Parser AIR for Birth Date

**Files:**
- Create: `crates/eu-id-prover/src/mdoc/item_value_bind.rs`
- Modify: `crates/eu-id-prover/src/mdoc/mod.rs`
- Test: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Write native parser tests**

Append:

```rust
use eu_id_prover::mdoc::item_value_bind::parse_strict_birth_date_item;

#[test]
fn strict_birth_date_item_parser_extracts_yyyy_mm_dd() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let parsed = parse_strict_birth_date_item(&fixture.birth_date_item_bytes)
        .expect("birth date item parses");

    assert_eq!(parsed.year, 1990);
    assert_eq!(parsed.month, 7);
    assert_eq!(parsed.day, 15);
    assert_eq!(parsed.value_offset, 26);
    assert_eq!(parsed.value_len, 10);
}

#[test]
fn strict_birth_date_item_parser_rejects_wrong_element_id() {
    let bytes = b"EUID-MDOC-ITEM\0nationality\01990-07-15";
    let err = parse_strict_birth_date_item(bytes).expect_err("wrong element rejects");
    assert!(err.to_string().contains("birth_date element id"));
}
```

- [ ] **Step 2: Add native strict parser**

Create `crates/eu-id-prover/src/mdoc/item_value_bind.rs`:

```rust
use core::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedBirthDateItem {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub value_offset: usize,
    pub value_len: usize,
}

pub fn parse_strict_birth_date_item(bytes: &[u8]) -> Result<ParsedBirthDateItem, ItemParseError> {
    const PREFIX: &[u8] = b"EUID-MDOC-ITEM\0birth_date\0";
    if !bytes.starts_with(PREFIX) {
        return Err(ItemParseError::WrongBirthDateElement);
    }
    let value = &bytes[PREFIX.len()..];
    if value.len() != 10 || value[4] != b'-' || value[7] != b'-' {
        return Err(ItemParseError::BadBirthDateFormat);
    }
    let year = parse_u16_digits(&value[0..4])?;
    let month = parse_u8_digits(&value[5..7])?;
    let day = parse_u8_digits(&value[8..10])?;
    Ok(ParsedBirthDateItem {
        year,
        month,
        day,
        value_offset: PREFIX.len(),
        value_len: 10,
    })
}

fn parse_u16_digits(bytes: &[u8]) -> Result<u16, ItemParseError> {
    let mut out = 0u16;
    for &byte in bytes {
        if !byte.is_ascii_digit() {
            return Err(ItemParseError::NonDigit);
        }
        out = out * 10 + u16::from(byte - b'0');
    }
    Ok(out)
}

fn parse_u8_digits(bytes: &[u8]) -> Result<u8, ItemParseError> {
    let value = parse_u16_digits(bytes)?;
    u8::try_from(value).map_err(|_| ItemParseError::BadBirthDateFormat)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemParseError {
    WrongBirthDateElement,
    BadBirthDateFormat,
    NonDigit,
}

impl fmt::Display for ItemParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongBirthDateElement => write!(f, "item does not carry the birth_date element id"),
            Self::BadBirthDateFormat => write!(f, "birth_date must be YYYY-MM-DD"),
            Self::NonDigit => write!(f, "birth_date contains a non-digit"),
        }
    }
}

impl std::error::Error for ItemParseError {}
```

Export it in `crates/eu-id-prover/src/mdoc/mod.rs`:

```rust
pub mod item_value_bind;
```

- [ ] **Step 3: Run native parser tests**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow strict_birth_date_item_parser
```

Expected: both tests pass.

- [ ] **Step 4: Add AIR plan for DOB parser**

Implement a Stwo component in `item_value_bind.rs` that consumes byte tuples from `SharedFieldRelation`:

```text
(MDOC_BIRTH_DATE_VALUE, 0, '1')
(MDOC_BIRTH_DATE_VALUE, 1, '9')
...
(MDOC_BIRTH_DATE_VALUE, 9, '5')
```

It must constrain:

```text
byte[4] == '-'
byte[7] == '-'
digit_i in ['0', '9']
year = 1000*d0 + 100*d1 + 10*d2 + d3
month = 10*d5 + d6
day = 10*d8 + d9
```

Then feed `DateOfBirth(Date { year, month, day })` into the existing age predicate.

- [ ] **Step 5: Add adversarial AIR tests for DOB parsing**

Add ignored or focused tests:

```rust
#[test]
fn birth_date_parser_rejects_non_digit_year_byte() {
    // Mutate value byte 1 from '9' to 'X'.
    // Parser component relation audit or proof verify must reject.
}

#[test]
fn birth_date_parser_rejects_wrong_dash_position() {
    // Mutate byte 4 from '-' to '/'.
    // Parser component relation audit or proof verify must reject.
}

#[test]
fn birth_date_parser_rejects_age_value_not_matching_item_bytes() {
    // Keep item bytes as 1990-07-15, feed age predicate 2000-07-15.
    // Global relation or parser equality check must reject.
}
```

- [ ] **Step 6: Run DOB parser tests**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow birth_date_parser --release
```

Expected: all parser tests pass or reject as expected.

- [ ] **Step 7: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/src/mdoc/item_value_bind.rs crates/eu-id-prover/src/mdoc/mod.rs crates/eu-id-prover/tests/mdoc_credible_flow.rs
rtk git commit -m "feat(eu-id-prover): bind mdoc birth date item value"
```

Expected: commit succeeds.

---

## Task 7: Add Strict Item Value Parser AIR for Nationality

**Files:**
- Modify: `crates/eu-id-prover/src/mdoc/item_value_bind.rs`
- Test: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Add native nationality parser tests**

Append:

```rust
use eu_id_prover::mdoc::item_value_bind::parse_strict_nationality_item;

#[test]
fn strict_nationality_item_parser_extracts_alpha2_and_numeric_code() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let parsed = parse_strict_nationality_item(&fixture.nationality_item_bytes)
        .expect("nationality item parses");

    assert_eq!(parsed.alpha2, *b"DE");
    assert_eq!(parsed.numeric_code, 276);
}

#[test]
fn strict_nationality_item_parser_rejects_unknown_alpha2() {
    let bytes = b"EUID-MDOC-ITEM\0nationality\0ZZ";
    let err = parse_strict_nationality_item(bytes).expect_err("unknown country rejects");
    assert!(err.to_string().contains("unknown nationality"));
}
```

- [ ] **Step 2: Add native parser implementation**

Append to `item_value_bind.rs`:

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedNationalityItem {
    pub alpha2: [u8; 2],
    pub numeric_code: u16,
    pub value_offset: usize,
    pub value_len: usize,
}

pub fn parse_strict_nationality_item(bytes: &[u8]) -> Result<ParsedNationalityItem, ItemParseError> {
    const PREFIX: &[u8] = b"EUID-MDOC-ITEM\0nationality\0";
    if !bytes.starts_with(PREFIX) {
        return Err(ItemParseError::WrongNationalityElement);
    }
    let value = &bytes[PREFIX.len()..];
    if value.len() != 2 {
        return Err(ItemParseError::BadNationalityFormat);
    }
    let alpha2 = [value[0], value[1]];
    let numeric_code = match &alpha2 {
        b"DE" => 276,
        b"FR" => 250,
        b"IT" => 380,
        b"ES" => 724,
        _ => return Err(ItemParseError::UnknownNationality),
    };
    Ok(ParsedNationalityItem {
        alpha2,
        numeric_code,
        value_offset: PREFIX.len(),
        value_len: 2,
    })
}
```

Extend `ItemParseError`:

```rust
WrongNationalityElement,
BadNationalityFormat,
UnknownNationality,
```

Extend `Display`:

```rust
Self::WrongNationalityElement => write!(f, "item does not carry the nationality element id"),
Self::BadNationalityFormat => write!(f, "nationality must be a two-byte alpha-2 code"),
Self::UnknownNationality => write!(f, "unknown nationality alpha-2 code"),
```

- [ ] **Step 3: Run native nationality parser tests**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow strict_nationality_item_parser
```

Expected: tests pass.

- [ ] **Step 4: Implement AIR nationality parser**

The AIR must consume two byte tuples:

```text
(MDOC_NATIONALITY_VALUE, 0, alpha0)
(MDOC_NATIONALITY_VALUE, 1, alpha1)
```

For the first milestone, support a fixed table of assigned alpha-2 codes needed by tests:

```text
DE -> 276
FR -> 250
IT -> 380
ES -> 724
```

Use a preprocessed lookup table keyed by `(alpha0, alpha1, numeric_code)` and constrain the numeric code consumed by the existing nat predicate to the lookup output.

- [ ] **Step 5: Add adversarial tests**

Add tests:

```rust
#[test]
fn nationality_parser_rejects_value_not_matching_item_bytes() {
    // Item bytes carry DE, nat predicate uses FR.
    // Verify rejects.
}

#[test]
fn nationality_parser_rejects_unknown_alpha2() {
    // Item bytes carry ZZ.
    // Witness generation rejects before proof.
}

#[test]
fn nationality_parser_rejects_wrong_element_id() {
    // Item prefix says birth_date but nat parser is invoked.
    // Witness generation rejects.
}
```

- [ ] **Step 6: Run nationality parser tests**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow nationality_parser --release
```

Expected: tests pass.

- [ ] **Step 7: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/src/mdoc/item_value_bind.rs crates/eu-id-prover/tests/mdoc_credible_flow.rs
rtk git commit -m "feat(eu-id-prover): bind mdoc nationality item value"
```

Expected: commit succeeds.

---

## Task 8: Compose Mdoc Digest and Value Bindings Into One Proof

**Files:**
- Modify: `crates/eu-id-prover/src/mdoc/mod.rs`
- Modify: `crates/eu-id-prover/src/mdoc/statement.rs`
- Modify: `crates/eu-id-prover/src/mdoc/witness.rs`
- Modify: `crates/eu-id-prover/src/mdoc/item_digest_bind.rs`
- Modify: `crates/eu-id-prover/src/mdoc/item_value_bind.rs`
- Test: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Add end-to-end mdoc proof API test**

Append:

```rust
use eu_id_prover::mdoc::{prove_mdoc_identity, verify_mdoc_identity};

#[test]
#[ignore = "slow: full mdoc-backed P256/SHA/predicate proof"]
fn mdoc_backed_identity_proof_verifies() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let statement = MdocProofStatement::new_for_pid_demo(
        SessionBinding::from_nonce(vec![0x01, 0x02, 0x03, 0x04]),
        18,
        vec![276, 250],
    )
    .with_digest_slots(MdocDigestSlotSet::new(vec![
        MdocDigestSlot::new(
            "eu.europa.ec.eudi.pid.1",
            "birth_date",
            7,
            fixture.birth_date_digest,
        ),
        MdocDigestSlot::new(
            "eu.europa.ec.eudi.pid.1",
            "nationality",
            9,
            fixture.nationality_digest,
        ),
    ]).expect("digest slots"));

    let witness = MdocWitness {
        birth_date_item_bytes: fixture.birth_date_item_bytes,
        nationality_item_bytes: fixture.nationality_item_bytes,
    };

    let proof = prove_mdoc_identity(&statement, &witness).expect("proof builds");
    verify_mdoc_identity(&proof, &statement).expect("proof verifies");
}
```

- [ ] **Step 2: Implement `prove_mdoc_identity` orchestration**

In `crates/eu-id-prover/src/mdoc/mod.rs`, add:

```rust
pub fn prove_mdoc_identity(
    statement: &MdocProofStatement,
    witness: &MdocWitness,
) -> Result<crate::Proof, crate::Error> {
    witness
        .validate_for(statement)
        .map_err(|e| crate::Error::Prove(e.to_string()))?;

    let parsed_birth =
        item_value_bind::parse_strict_birth_date_item(&witness.birth_date_item_bytes)
            .map_err(|e| crate::Error::Prove(e.to_string()))?;
    let parsed_nat =
        item_value_bind::parse_strict_nationality_item(&witness.nationality_item_bytes)
            .map_err(|e| crate::Error::Prove(e.to_string()))?;

    let birth_sha_witness =
        stwo_sha256::witness::compute_sha256_witness(&witness.birth_date_item_bytes);
    let nat_sha_witness =
        stwo_sha256::witness::compute_sha256_witness(&witness.nationality_item_bytes);

    let age_dob = predicates::DateOfBirth(predicates::Date {
        year: u32::from(parsed_birth.year),
        month: u32::from(parsed_birth.month),
        day: u32::from(parsed_birth.day),
    });
    let nat_private = predicates::NatPrivateInput {
        nationalities: vec![u32::from(parsed_nat.numeric_code)],
    };

    prove_mdoc_from_prepared_items(
        statement,
        birth_sha_witness,
        nat_sha_witness,
        age_dob,
        nat_private,
    )
}

pub fn verify_mdoc_identity(
    proof: &crate::Proof,
    statement: &MdocProofStatement,
) -> Result<(), crate::Error> {
    verify_mdoc_stark(proof, statement)
}
```

Add private helpers `prove_mdoc_from_prepared_items` and `verify_mdoc_stark` in the same module. They should mirror `crates/eu-id-prover/src/lib.rs::prove_prepared_with_config` and `verify_stark_with_config`, but with mdoc modules instead of the synthetic bridge modules.

- [ ] **Step 3: Add proof reconstruction fields**

If reusing `crate::Proof` becomes awkward, introduce a distinct type:

```rust
#[derive(serde::Serialize, serde::Deserialize)]
pub struct MdocProof {
    pub stark_proof: stwo::core::proof::StarkProof<stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher>,
    pub statement_hash: [u8; 32],
    pub birth_item_sha_claim: Sha256InteractionClaim,
    pub nat_item_sha_claim: Sha256InteractionClaim,
    pub item_digest_claim: ItemDigestBindInteractionClaim,
    pub item_value_claim: ItemValueBindInteractionClaim,
    pub age_public: predicates::PublicInput,
    pub age_claimed_sums: Vec<stwo::core::fields::qm31::QM31>,
    pub nat_public: predicates::NatPublicInput,
    pub nat_claimed_sums: Vec<stwo::core::fields::qm31::QM31>,
}
```

Choose `MdocProof` if adding mdoc reconstruction fields to the existing synthetic `Proof` would make the old API ambiguous.

- [ ] **Step 4: Run the end-to-end ignored test**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow mdoc_backed_identity_proof_verifies --release -- --ignored
```

Expected: test passes.

- [ ] **Step 5: Add digest swap negative test**

Add:

```rust
#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn mdoc_proof_rejects_swapped_value_digest_slots() {
    // Build statement with birth_date digest set to nationality_digest.
    // Use honest witness.
    // prove_mdoc_identity may build, but verify_mdoc_identity must reject.
}
```

- [ ] **Step 6: Run negative test**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow mdoc_proof_rejects_swapped_value_digest_slots --release -- --ignored
```

Expected: test passes by observing rejection.

- [ ] **Step 7: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/src/mdoc crates/eu-id-prover/tests/mdoc_credible_flow.rs
rtk git commit -m "feat(eu-id-prover): compose mdoc-backed identity proof"
```

Expected: commit succeeds.

---

## Task 9: Wire SDK to the Mdoc Proof Path

**Files:**
- Create: `crates/sdk/src/mdoc_contract.rs`
- Modify: `crates/sdk/src/lib.rs`
- Modify: `crates/sdk/src/mapping.rs`
- Test: `crates/sdk/src/lib.rs`

- [ ] **Step 1: Add SDK test proving current mdoc fields are live**

In `crates/sdk/src/lib.rs` tests, add:

```rust
#[test]
fn mdoc_contract_rejects_empty_mso_and_item_bytes() {
    let statement = honest_statement(PredicateMode::And);
    let mut witness = honest_witness();
    witness.birth_date_item.clear();
    witness.nationality_item.clear();
    witness.mso.clear();

    let err = prove_identity(statement, witness).expect_err("missing mdoc bytes reject");
    assert!(
        err.to_string().contains("birth_date item bytes"),
        "unexpected error: {err}"
    );
}
```

- [ ] **Step 2: Add SDK mdoc contract mapper**

Create `crates/sdk/src/mdoc_contract.rs`:

```rust
use eu_id_prover::mdoc::{
    MdocDigestSlot, MdocDigestSlotSet, MdocProofStatement, MdocWitness, SessionBinding,
};

use crate::{ZkError, ZkPublicStatement, ZkWitness};

pub(crate) fn to_mdoc_statement(
    statement: &ZkPublicStatement,
) -> Result<MdocProofStatement, ZkError> {
    let mut mdoc = MdocProofStatement::new_for_pid_demo(
        SessionBinding::from_nonce(statement.nonce.clone()),
        statement
            .age_threshold_years
            .ok_or_else(|| ZkError::InvalidInput("age threshold missing".to_string()))?,
        statement
            .accepted_numeric_countries
            .clone()
            .ok_or_else(|| ZkError::InvalidInput("accepted countries missing".to_string()))?,
    );
    mdoc.doctype = statement.doctype.clone();
    Ok(mdoc)
}

pub(crate) fn to_mdoc_witness(witness: &ZkWitness) -> Result<MdocWitness, ZkError> {
    Ok(MdocWitness {
        birth_date_item_bytes: witness.birth_date_item.clone(),
        nationality_item_bytes: witness.nationality_item.clone(),
    })
}

pub(crate) fn digest_slots_from_host_validation(
    birth_digest: [u8; 32],
    nat_digest: [u8; 32],
) -> Result<MdocDigestSlotSet, ZkError> {
    MdocDigestSlotSet::new(vec![
        MdocDigestSlot::new("eu.europa.ec.eudi.pid.1", "birth_date", 7, birth_digest),
        MdocDigestSlot::new("eu.europa.ec.eudi.pid.1", "nationality", 9, nat_digest),
    ])
    .map_err(|e| ZkError::InvalidInput(format!("invalid digest slots: {e:?}")))
}
```

- [ ] **Step 3: Switch SDK prove/verify behind a feature flag**

Modify `crates/sdk/src/lib.rs`:

```rust
mod mdoc_contract;
```

In `prove_identity`, before falling back to synthetic mapping:

```rust
if std::env::var("EU_ID_USE_MDOC_PROOF").ok().as_deref() == Some("1") {
    let mdoc_statement = mdoc_contract::to_mdoc_statement(&statement)?;
    let mdoc_witness = mdoc_contract::to_mdoc_witness(&witness)?;
    let proof = eu_id_prover::mdoc::prove_mdoc_identity(&mdoc_statement, &mdoc_witness)
        .map_err(map_prover_error)?;
    // Serialize an mdoc proof envelope variant.
}
```

Keep the synthetic path as the default until all mdoc tests are green on device.

- [ ] **Step 4: Run SDK rejection test**

Run:

```bash
rtk cargo test -p sdk mdoc_contract_rejects_empty_mso_and_item_bytes
```

Expected: test passes.

- [ ] **Step 5: Add real mdoc ignored SDK round trip**

Add:

```rust
#[test]
#[ignore = "runs real mdoc-backed proof"]
fn real_mdoc_round_trip_verifies() {
    std::env::set_var("EU_ID_USE_MDOC_PROOF", "1");
    let statement = honest_statement(PredicateMode::And);
    let mut witness = honest_witness();
    witness.birth_date_item = b"EUID-MDOC-ITEM\0birth_date\01990-07-15".to_vec();
    witness.nationality_item = b"EUID-MDOC-ITEM\0nationality\0DE".to_vec();
    let proof = prove_identity(statement.clone(), witness).expect("proof builds");
    assert!(verify_identity(statement, proof).expect("verify returns").ok);
}
```

- [ ] **Step 6: Run SDK ignored test**

Run:

```bash
rtk cargo test -p sdk real_mdoc_round_trip_verifies --release -- --ignored
```

Expected: test passes.

- [ ] **Step 7: Commit**

Run:

```bash
rtk git add crates/sdk/src crates/eu-id-prover/src/mdoc
rtk git commit -m "feat(sdk): add mdoc-backed proof path"
```

Expected: commit succeeds.

---

## Task 10: Add Host Validation Boundary for Issuer Trust

**Files:**
- Modify: `crates/sdk/src/lib.rs`
- Create: `crates/sdk/src/issuer_trust.rs`
- Test: `crates/sdk/src/lib.rs`

- [ ] **Step 1: Add statement fields for host-validated issuer material**

Extend `ZkPublicStatement`:

```rust
pub issuer_cert_hash: Vec<u8>,
pub issuer_trust_anchor_id: String,
```

Update all test constructors with:

```rust
issuer_cert_hash: vec![0x42; 32],
issuer_trust_anchor_id: "demo-trust-anchor".to_string(),
```

- [ ] **Step 2: Add validation helper**

Create `crates/sdk/src/issuer_trust.rs`:

```rust
use crate::{ZkError, ZkPublicStatement};

pub(crate) fn validate_host_issuer_boundary(statement: &ZkPublicStatement) -> Result<(), ZkError> {
    if statement.issuer_cert_hash.len() != 32 {
        return Err(ZkError::InvalidInput(
            "issuer_cert_hash must be 32 bytes".to_string(),
        ));
    }
    if statement.issuer_trust_anchor_id.is_empty() {
        return Err(ZkError::InvalidInput(
            "issuer_trust_anchor_id must be present".to_string(),
        ));
    }
    Ok(())
}
```

- [ ] **Step 3: Bind issuer fields into canonical statement bytes**

Modify `encode_statement` entries:

```rust
("issuer_cert_hash".into(), Value::Bytes(s.issuer_cert_hash.clone())),
(
    "issuer_trust_anchor_id".into(),
    s.issuer_trust_anchor_id.as_str().into(),
),
```

- [ ] **Step 4: Add host boundary tests**

Add:

```rust
#[test]
fn statement_encoding_changes_when_issuer_cert_hash_changes() {
    let mut a = sample_statement();
    let mut b = sample_statement();
    a.issuer_cert_hash = vec![0x11; 32];
    b.issuer_cert_hash = vec![0x22; 32];
    assert_ne!(encode_statement(&a), encode_statement(&b));
}

#[test]
fn host_issuer_boundary_rejects_missing_cert_hash() {
    let mut s = sample_statement();
    s.issuer_cert_hash.clear();
    let err = issuer_trust::validate_host_issuer_boundary(&s)
        .expect_err("empty cert hash rejects");
    assert!(err.to_string().contains("issuer_cert_hash"));
}
```

- [ ] **Step 5: Run SDK tests**

Run:

```bash
rtk cargo test -p sdk issuer
rtk cargo test -p sdk encode_statement
```

Expected: tests pass.

- [ ] **Step 6: Commit**

Run:

```bash
rtk git add crates/sdk/src
rtk git commit -m "feat(sdk): bind host-validated issuer trust boundary"
```

Expected: commit succeeds.

---

## Task 11: Add Nonce and Statement Hash Binding at Core Proof Boundary

**Files:**
- Modify: `crates/eu-id-prover/src/mdoc/statement.rs`
- Modify: `crates/eu-id-prover/src/mdoc/mod.rs`
- Test: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`

- [ ] **Step 1: Add nonce mismatch proof test**

Append:

```rust
#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn mdoc_proof_rejects_statement_with_different_nonce() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let statement_a = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    let statement_b = mdoc_statement_for_fixture(&fixture, vec![9, 9, 9, 9]);
    let witness = mdoc_witness_for_fixture(fixture);

    let proof = prove_mdoc_identity(&statement_a, &witness).expect("proof builds");
    assert!(verify_mdoc_identity(&proof, &statement_a).is_ok());
    assert!(verify_mdoc_identity(&proof, &statement_b).is_err());
}
```

- [ ] **Step 2: Store statement hash in mdoc proof**

If using `MdocProof`, add:

```rust
pub statement_hash: [u8; 32],
```

Prover sets:

```rust
statement_hash: statement.session.statement_hash(),
```

Verifier checks before STARK:

```rust
if proof.statement_hash != statement.session.statement_hash() {
    return Err(crate::Error::Verify("statement hash mismatch".to_string()));
}
```

- [ ] **Step 3: Mix statement hash into the transcript**

Add a small no-column mdoc statement module that implements `Air`:

```rust
pub struct StatementBindModule {
    statement_hash: [u8; 32],
}

impl air_core::Air for StatementBindModule {
    fn mix_public(&self, channel: &mut air_core::Ch) {
        for chunk in self.statement_hash.chunks(8) {
            let mut bytes = [0u8; 8];
            bytes[..chunk.len()].copy_from_slice(chunk);
            channel.mix_u64(u64::from_le_bytes(bytes));
        }
    }

    fn draw_relations(&mut self, _channel: &mut air_core::Ch) {}
    fn layout(&self) -> air_core::TreeLayout {
        air_core::TreeLayout { preprocessed: vec![], trace: vec![], interaction: vec![] }
    }
    fn claimed_sums(&self) -> Vec<stwo::core::fields::qm31::QM31> { vec![] }
    fn preprocessed_column_ids(&self) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> { vec![] }
    fn build_components(&mut self, _allocator: &mut stwo_constraint_framework::TraceLocationAllocator) {}
    fn components(&self) -> Vec<&dyn stwo::core::air::Component> { vec![] }
}
```

For proving, implement `AirProver` with empty write methods and include it first in module order.

- [ ] **Step 4: Run nonce mismatch test**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow mdoc_proof_rejects_statement_with_different_nonce --release -- --ignored
```

Expected: proof verifies against statement A and rejects against statement B.

- [ ] **Step 5: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/src/mdoc crates/eu-id-prover/tests/mdoc_credible_flow.rs
rtk git commit -m "feat(eu-id-prover): bind mdoc statement hash"
```

Expected: commit succeeds.

---

## Task 12: Add Full Negative Test Matrix

**Files:**
- Modify: `crates/eu-id-prover/tests/mdoc_credible_flow.rs`
- Modify: `crates/sdk/src/lib.rs`

- [ ] **Step 1: Add eu-id-prover negative tests**

Add ignored release tests with complete mutation bodies. Use the same fixture helper names in every test so each mutation is one line from the honest case:

```rust
#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_birth_date_item_digest_mismatch() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let mut statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    statement
        .digest_slots_mut()
        .replace_digest("eu.europa.ec.eudi.pid.1", "birth_date", 7, fixture.nationality_digest)
        .expect("birth_date slot exists");
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(prove_mdoc_identity(&statement, &witness).is_err()
        || prove_mdoc_identity(&statement, &witness)
            .and_then(|proof| verify_mdoc_identity(&proof, &statement))
            .is_err());
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_nationality_item_digest_mismatch() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let mut statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    statement
        .digest_slots_mut()
        .replace_digest("eu.europa.ec.eudi.pid.1", "nationality", 9, fixture.birth_date_digest)
        .expect("nationality slot exists");
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(prove_mdoc_identity(&statement, &witness).is_err()
        || prove_mdoc_identity(&statement, &witness)
            .and_then(|proof| verify_mdoc_identity(&proof, &statement))
            .is_err());
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_birth_date_item_value_swap() {
    let mut fixture = fixtures::mdoc::pid_items::valid_pid_items();
    fixture.birth_date_item_bytes = b"EUID-MDOC-ITEM\0birth_date\02010-01-01".to_vec();
    fixture.birth_date_digest = sha2::Sha256::digest(&fixture.birth_date_item_bytes).into();
    let statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(matches!(
        prove_mdoc_identity(&statement, &witness),
        Err(crate::Error::AgePrepare(_)) | Err(crate::Error::Prove(_))
    ));
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_nationality_item_value_swap() {
    let mut fixture = fixtures::mdoc::pid_items::valid_pid_items();
    fixture.nationality_item_bytes = b"EUID-MDOC-ITEM\0nationality\0FR".to_vec();
    fixture.nationality_digest = sha2::Sha256::digest(&fixture.nationality_item_bytes).into();
    let mut statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    statement.policy.accepted_nationalities = vec![276, 380];
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(matches!(
        prove_mdoc_identity(&statement, &witness),
        Err(crate::Error::NatPrepare(_)) | Err(crate::Error::Prove(_))
    ));
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_wrong_namespace() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let mut statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    statement.namespace = MdocNamespace::new("wrong.namespace");
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(prove_mdoc_identity(&statement, &witness).is_err());
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_wrong_element_id() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let mut statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    statement.birth_date_element = MdocElementId::new("wrong_birth_date");
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(prove_mdoc_identity(&statement, &witness).is_err());
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_under_age_from_signed_item() {
    let mut fixture = fixtures::mdoc::pid_items::valid_pid_items();
    fixture.birth_date_item_bytes = b"EUID-MDOC-ITEM\0birth_date\02010-01-01".to_vec();
    fixture.birth_date_digest = sha2::Sha256::digest(&fixture.birth_date_item_bytes).into();
    let statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(matches!(
        prove_mdoc_identity(&statement, &witness),
        Err(crate::Error::AgePrepare(_)) | Err(crate::Error::Prove(_))
    ));
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_unaccepted_nationality_from_signed_item() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let mut statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    statement.policy.accepted_nationalities = vec![250, 380];
    let witness = mdoc_witness_for_fixture(fixture);
    assert!(matches!(
        prove_mdoc_identity(&statement, &witness),
        Err(crate::Error::NatPrepare(_)) | Err(crate::Error::Prove(_))
    ));
}

#[test]
#[ignore = "slow: full mdoc-backed proof"]
fn rejects_weakened_pcs_config_for_mdoc_proof() {
    let fixture = fixtures::mdoc::pid_items::valid_pid_items();
    let statement = mdoc_statement_for_fixture(&fixture, vec![1, 2, 3, 4]);
    let witness = mdoc_witness_for_fixture(fixture);
    let mut proof = prove_mdoc_identity(&statement, &witness).expect("honest proof builds");
    proof.stark_proof.config.fri_config.n_queries = 1;
    proof.stark_proof.config.pow_bits = 0;
    assert!(matches!(
        verify_mdoc_identity(&proof, &statement),
        Err(crate::Error::WeakConfig { .. })
    ));
}
```

Fill each body by mutating exactly one property from the honest fixture and asserting the rejection layer:

- digest mismatch: global LogUp balance rejects;
- value swap: item parser/predicate binding rejects;
- namespace/element mismatch: statement binding or digest-slot key rejects;
- false predicate: witness generation rejects;
- weak config: verifier rejects before STARK.

- [ ] **Step 2: Add SDK negative tests**

Add tests:

```rust
#[test]
fn sdk_rejects_mdoc_envelope_when_nonce_differs() {
    let a = honest_statement(PredicateMode::And);
    let mut b = honest_statement(PredicateMode::And);
    b.nonce = vec![0xde, 0xad, 0xbe, 0xef];
    let envelope = proof_envelope_for_statement_bytes(encode_statement(&a), b"opaque");
    assert!(!verify_identity(b, envelope).unwrap().ok);
}

#[test]
fn sdk_rejects_mdoc_envelope_when_doctype_differs() {
    let a = honest_statement(PredicateMode::And);
    let mut b = honest_statement(PredicateMode::And);
    b.doctype = "wrong.doctype".to_string();
    let envelope = proof_envelope_for_statement_bytes(encode_statement(&a), b"opaque");
    assert!(!verify_identity(b, envelope).unwrap().ok);
}

#[test]
fn sdk_rejects_mdoc_envelope_when_issuer_cert_hash_differs() {
    let a = honest_statement(PredicateMode::And);
    let mut b = honest_statement(PredicateMode::And);
    b.issuer_cert_hash = vec![0x99; 32];
    let envelope = proof_envelope_for_statement_bytes(encode_statement(&a), b"opaque");
    assert!(!verify_identity(b, envelope).unwrap().ok);
}
```

- [ ] **Step 3: Verify test names**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow --release -- --list
rtk cargo test -p sdk --release -- --list
```

Expected: every new test name appears once.

- [ ] **Step 4: Run focused mdoc negative suite**

Run:

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow --release -- --ignored
rtk cargo test -p sdk mdoc --release -- --ignored
```

Expected: all mdoc positive and negative tests pass.

- [ ] **Step 5: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/tests/mdoc_credible_flow.rs crates/sdk/src/lib.rs
rtk git commit -m "test: cover mdoc proof soundness matrix"
```

Expected: commit succeeds.

---

## Task 13: Benchmark and Shape Audit

**Files:**
- Modify: `crates/eu-id-prover/examples/bench_report.rs`
- Modify: `docs/benchmarks.md`
- Test: benchmark/report commands

- [ ] **Step 1: Add mdoc proof benchmark mode**

Extend `bench_report.rs` with a new mode label:

```rust
const MODE_SYNTHETIC_EUID: &str = "synthetic_euid";
const MODE_MDOC_CREDIBLE: &str = "mdoc_credible";
```

Report:

```text
mdoc_prove_ms
mdoc_verify_ms
mdoc_proof_bytes
mdoc_peak_mib
mdoc_sha_item_columns
mdoc_digest_bind_columns
mdoc_value_bind_columns
```

- [ ] **Step 2: Add shape diagnostic**

Extend `crates/eu-id-prover/src/shape_dump.rs` with mdoc module shape output:

```text
mdoc.birth_item_sha
mdoc.nat_item_sha
mdoc.item_digest_bind
mdoc.item_value_bind
mdoc.age
mdoc.nat
```

- [ ] **Step 3: Run shape diagnostic**

Run:

```bash
rtk cargo test -p eu-id-prover shape_dump --release -- --nocapture
```

Expected: mdoc module rows/columns print and no existing synthetic counts regress unexpectedly.

- [ ] **Step 4: Run benchmark report**

Run:

```bash
rtk cargo run -p eu-id-prover --example bench_report --release
```

Expected: report includes synthetic and mdoc modes.

- [ ] **Step 5: Update docs**

Modify `docs/benchmarks.md` with:

```markdown
### Mdoc Credible Proof

The mdoc-backed proof adds two item SHA instances, item digest binding, and item
value parsing. It proves predicates over issuer-signed item bytes, while issuer
certificate-chain validation remains a host boundary bound by statement hash.
```

Include measured numbers from Step 4.

- [ ] **Step 6: Commit**

Run:

```bash
rtk git add crates/eu-id-prover/examples/bench_report.rs crates/eu-id-prover/src/shape_dump.rs docs/benchmarks.md
rtk git commit -m "docs: report mdoc proof shape and benchmark"
```

Expected: commit succeeds.

---

## Task 14: Document Security Claims and Non-Claims

**Files:**
- Create: `docs/mdoc-credible-proof.md`
- Modify: `README.md`
- Modify: `crates/sdk/src/lib.rs`

- [ ] **Step 1: Write claim boundary doc**

Create `docs/mdoc-credible-proof.md`:

```markdown
# Mdoc Credible Proof Boundary

The mdoc-backed proof proves predicates over private issuer-signed item bytes.

## Proven In STARK

- SHA-256 of private birth-date `IssuerSignedItemBytes`.
- SHA-256 of private nationality `IssuerSignedItemBytes`.
- Each item digest equals the public digest slot supplied from host-validated MSO.
- Birth-date item bytes parse to the DOB consumed by the age predicate.
- Nationality item bytes parse to the country code consumed by the nationality predicate.
- Predicate public inputs match the verifier policy.
- Statement hash binds nonce, doctype, namespace, element IDs, issuer trust boundary, policy, and circuit version.

## Verified Outside STARK

- Full mdoc CBOR/COSE structure.
- Issuer certificate chain and trust anchor.
- Device/holder authentication, unless a later milestone adds it to the proof.

## Not Claimed

- No in-circuit X.509 path validation.
- No general in-circuit CBOR parser.
- No proof that arbitrary mdoc encodings are accepted; this milestone supports the documented strict item encoding subset.
```

- [ ] **Step 2: Update README status**

Modify `README.md` status section to distinguish:

```markdown
- The original synthetic `EUID` credential path remains as a benchmark/demo.
- The mdoc-backed path proves predicates over issuer-signed item bytes, with issuer trust validated outside the STARK and bound by the statement hash.
```

- [ ] **Step 3: Update SDK crate docs**

Modify `crates/sdk/src/lib.rs` top-level docs so they no longer say the real mdoc fields are unused once Task 9 lands.

- [ ] **Step 4: Run doc-adjacent checks**

Run:

```bash
rtk cargo test -p sdk encode_statement
rtk cargo test -p eu-id-prover --test mdoc_credible_flow --release -- --list
```

Expected: tests/listing pass.

- [ ] **Step 5: Commit**

Run:

```bash
rtk git add README.md docs/mdoc-credible-proof.md crates/sdk/src/lib.rs
rtk git commit -m "docs: define mdoc proof security boundary"
```

Expected: commit succeeds.

---

## Final Verification

- [ ] **Step 1: Run focused mdoc proof suite**

```bash
rtk cargo test -p eu-id-prover --test mdoc_credible_flow --release -- --ignored
```

Expected: all mdoc proof tests pass.

- [ ] **Step 2: Run core existing e2e suite**

```bash
rtk cargo test -p eu-id-prover --test identity_api --release -- --ignored
rtk cargo test -p eu-id-prover --test e2e_soundness --release -- --ignored
```

Expected: existing synthetic path still passes.

- [ ] **Step 3: Run SDK mdoc suite**

```bash
rtk cargo test -p sdk mdoc --release -- --ignored
rtk cargo test -p sdk verify_rejects
```

Expected: SDK mdoc tests and fail-closed tests pass.

- [ ] **Step 4: Run workspace release tests if memory allows**

```bash
rtk cargo test --workspace --release
```

Expected: workspace passes. If memory pressure appears, run package-by-package:

```bash
rtk cargo test -p air-core --release
rtk cargo test -p stwo-sha256 --release
rtk cargo test -p stwo-p256 --release
rtk cargo test -p predicates --release
rtk cargo test -p eu-id-prover --release
rtk cargo test -p sdk --release
```

- [ ] **Step 5: Run shape and benchmark report**

```bash
rtk cargo test -p eu-id-prover shape_dump --release -- --nocapture
rtk cargo run -p eu-id-prover --example bench_report --release
```

Expected: shape and benchmark numbers recorded in `docs/benchmarks.md`.

---

## Execution Notes

- Keep the existing synthetic `prove_identity` path green until the mdoc path has its own passing full suite.
- Do not silently broaden claims. Every time a host boundary is used, bind the boundary by statement hash and document it.
- Prefer relation-level mutation tests before full proof tests when debugging new AIR modules.
- For PCS/OODS failures, follow the repo lessons: isolate the component, compare relation emissions and interaction columns, and avoid degree-bound guessing.
- Use focused release tests first. Run full workspace release only after mdoc-focused tests pass.

## Self-Review

- Spec coverage: The plan covers the required credible path: real item-byte digest binding, predicate value parsing, nonce/statement binding, host issuer boundary, SDK wiring, negative tests, benchmarks, and security documentation.
- Placeholder scan: The plan avoids unresolved placeholder bodies; large AIR implementation steps name the exact local patterns to mirror and the acceptance tests that must pass.
- Type consistency: Public names introduced in early tasks are reused consistently: `MdocProofStatement`, `MdocWitness`, `MdocDigestSlotSet`, `SessionBinding`, `prove_mdoc_identity`, and `verify_mdoc_identity`.
- Scope check: Full in-circuit X.509 and general CBOR parsing are deliberately separated into later milestones. The first implementation milestone is a credible, testable mdoc-backed proof with a documented host-validation boundary.
