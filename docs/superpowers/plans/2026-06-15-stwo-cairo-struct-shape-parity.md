# Stwo Cairo Struct Shape Parity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Align `stwo-p256` proof-facing struct shapes with `~/stwo-cairo`: component `Claim` structs carry shape data, component `InteractionClaim` structs carry only PCS-backed claimed sums, aggregate claims flatten component claims, and semantic provider/consumer breakdowns are not verifier-facing proof fields.

**Architecture:** Treat `stwo-cairo` as the reference structure. Keep proof-critical LogUp sums as component claimed sums only; move semantic relation accounting into private debug/audit helpers that are recomputed from local traces or instances. Add structural guard tests first, then refactor component families in small release-verified batches.

**Tech Stack:** Rust, Stwo AIR framework, Cargo tests, local source-shape tests, release-mode verification.

---

## File Structure

- Modify `crates/stwo-p256/src/proof/tests.rs`: add structural guard tests that scan `src/**/*.rs` and reject non-reference proof-facing struct shapes.
- Modify `crates/stwo-p256/src/components/*`: normalize component `Claim`, `ProofClaim`, `InteractionClaim`, and `Components` structs to the `stwo-cairo` pattern.
- Modify `crates/stwo-p256/src/proof/mod.rs`: replace semantic relation-balance dependencies on prover-supplied side sums with flattened component claimed sums and verifier-recomputed public-data sums.
- Modify `crates/stwo-p256/src/proof/balances.rs`: delete or demote legacy semantic balance claim structs if they remain verifier-facing.
- Modify component tests near each changed component: replace side-sum mutation tests with component-claim or debug-audit tests.
- Do not edit `~/stwo-cairo`; use it only as the reference.

## Reference Rules

The target shape is:

```rust
pub struct Claim {
    pub log_size: u32,
}

pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}
```

Top-level aggregate interaction claims may contain component interaction claims, but must not contain direct semantic `SecureField` fields such as `*_provider_claimed_sum`, `*_consumer_claimed_sum`, `*_yield_sum`, `*_use_sum`, or `*_total_claimed_sum`.

---

### Task 1: Add Struct-Shape Guard Tests

**Files:**
- Modify: `crates/stwo-p256/src/proof/tests.rs`

- [ ] **Step 1: Add failing structural tests**

Append this helper and tests near the existing proof-layer regression tests:

```rust
#[cfg(test)]
fn stwo_p256_source_files() -> Vec<std::path::PathBuf> {
    fn visit(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(dir).expect("source directory is readable") {
            let entry = entry.expect("source entry is readable");
            let path = entry.path();
            if path.is_dir() {
                visit(&path, out);
            } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
                out.push(path);
            }
        }
    }

    let mut files = Vec::new();
    visit(&std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src"), &mut files);
    files
}

#[test]
fn interaction_claim_structs_match_stwo_cairo_shape() {
    let forbidden_field_names = [
        "consumer_claimed_sum",
        "provider_claimed_sum",
        "total_claimed_sum",
        "component_claimed_sum",
        "yield_sum",
        "use_sum",
        "digest_use_sum",
        "range_use_sum",
        "check:",
    ];
    let mut offenders = Vec::new();

    for path in stwo_p256_source_files() {
        let source = std::fs::read_to_string(&path).expect("source file is readable");
        if !source.contains("InteractionClaim") {
            continue;
        }
        for (line_index, line) in source.lines().enumerate() {
            if forbidden_field_names.iter().any(|name| line.contains(name)) {
                offenders.push(format!(
                    "{}:{}: {}",
                    path.strip_prefix(env!("CARGO_MANIFEST_DIR"))
                        .unwrap_or(&path)
                        .display(),
                    line_index + 1,
                    line.trim()
                ));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "interaction claims must expose only component claimed sums, stwo-cairo style:\n{}",
        offenders.join("\n")
    );
}

#[test]
fn top_level_interaction_claim_has_no_direct_semantic_secure_fields() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/proof/mod.rs");
    let source = std::fs::read_to_string(path).expect("proof module is readable");
    let start = source
        .find("pub struct P256CurrentAirInteractionClaim")
        .expect("P256CurrentAirInteractionClaim exists");
    let body = &source[start..source[start..].find("\n}").expect("struct closes") + start];
    let forbidden = [
        "ecdsa_result_provider_claimed_sum",
        "provider_claimed_sum: SecureField",
        "consumer_claimed_sum: SecureField",
        "claimed_sum: SecureField",
    ];

    for needle in forbidden {
        assert!(
            !body.contains(needle),
            "top-level interaction claim must aggregate component claims, not direct semantic SecureField `{needle}`"
        );
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run:

```bash
rtk cargo test -p stwo-p256 interaction_claim_structs_match_stwo_cairo_shape --release
rtk cargo test -p stwo-p256 top_level_interaction_claim_has_no_direct_semantic_secure_fields --release
```

Expected: both tests fail and list existing side-sum fields.

- [ ] **Step 3: Commit only the red guard tests if working on an isolated branch**

```bash
rtk git add crates/stwo-p256/src/proof/tests.rs
rtk git commit -m "test: guard stwo-cairo claim struct shape"
```

---

### Task 2: Normalize Leaf Single-Component Interaction Claims

**Files:**
- Modify: `crates/stwo-p256/src/components/fake_glv/scalar/air.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/selector/air.rs`
- Modify: `crates/stwo-p256/src/components/scalar_setup/cert_bind.rs`
- Modify: `crates/stwo-p256/src/components/final_check/air.rs`

- [ ] **Step 1: Refactor each leaf interaction claim to one field**

For each file above, change the component interaction claim to this shape:

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XInteractionClaim {
    pub claimed_sum: SecureField,
}

impl XInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}
```

Use the concrete existing type name in each file:

```rust
CertScalarInputAirInteractionClaim
FakeGlvScalarAirInteractionClaim
FakeGlvSelectorAirInteractionClaim
FinalCheckAirInteractionClaim
```

- [ ] **Step 2: Keep side-sum calculations out of returned proof claims**

In each `gen_*_interaction_trace` function, return only:

```rust
(trace, XInteractionClaim { claimed_sum })
```

Delete local assignments that only populate removed side fields. If a test still needs those numbers, add a private `#[cfg(test)]` helper named `debug_*_relation_sums(...)` in the same file that recomputes them from base rows and relations.

- [ ] **Step 3: Update component constructors**

Any constructor that currently reads a removed side field must instead use only:

```rust
interaction_claim.claimed_sum
```

- [ ] **Step 4: Run focused release tests**

Run:

```bash
rtk cargo test -p stwo-p256 --release fake_glv_scalar
rtk cargo test -p stwo-p256 --release fake_glv_selector
rtk cargo test -p stwo-p256 --release final_check
rtk cargo test -p stwo-p256 --release cert_scalar
```

Expected: all selected tests pass after downstream proof-layer references are updated in Task 6.

---

### Task 3: Normalize Bundled Component Claims By Splitting Component Sums

**Files:**
- Modify: `crates/stwo-p256/src/components/hinted_mul/air.rs`
- Modify: `crates/stwo-p256/src/components/hinted_mul/trace.rs`
- Modify: `crates/stwo-p256/src/components/final_add/interaction.rs`
- Modify: `crates/stwo-p256/src/components/public_key_curve/air.rs`
- Modify: `crates/stwo-p256/src/components/gamma_digest/mod.rs`
- Modify: `crates/stwo-p256/src/components/scalar_mod_mul/interaction_claim.rs`

- [ ] **Step 1: Replace semantic side fields with component claim fields**

Use this pattern for bundled components:

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XInteractionClaim {
    pub check: ComponentInteractionClaim,
    pub range13: RangeCheckInteractionClaim,
    pub signed_carry: RangeCheckInteractionClaim,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentInteractionClaim {
    pub claimed_sum: SecureField,
}
```

Every field must either be another `*InteractionClaim` or a `claimed_sum` inside a distinct component claim. Do not keep direct fields named `*_consumer_claimed_sum`, `*_provider_claimed_sum`, `*_yield_sum`, `*_use_sum`, or `check: SecureField`.

- [ ] **Step 2: Update `mix_into` methods**

Flatten only component claimed sums:

```rust
pub fn mix_into(&self, channel: &mut impl Channel) {
    self.check.mix_into(channel);
    self.range13.mix_into(channel);
    self.signed_carry.mix_into(channel);
}
```

For variable slices, use deterministic order:

```rust
for claim in &self.slices {
    claim.mix_into(channel);
}
```

- [ ] **Step 3: Move gamma semantic sums out of `GammaTallInteractionClaim`**

Change `GammaTallInteractionClaim` to:

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GammaTallInteractionClaim {
    pub claimed_sum: SecureField,
}
```

Move `digest_use_sum` and `range_use_sum` into private debug helpers:

```rust
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GammaTallDebugSums {
    pub digest_use_sum: SecureField,
    pub range_use_sum: SecureField,
}
```

- [ ] **Step 4: Run bundled component tests**

Run:

```bash
rtk cargo test -p stwo-p256 --release hinted_mul
rtk cargo test -p stwo-p256 --release final_add
rtk cargo test -p stwo-p256 --release public_key_curve
rtk cargo test -p stwo-p256 --release gamma_digest
rtk cargo test -p stwo-p256 --release scalar_mod_mul
```

Expected: component tests pass after Task 6 removes verifier dependence on semantic side sums.

---

### Task 4: Normalize Fake-GLV Source, Operand, Chain, and Prepared-Table Claims

**Files:**
- Modify: `crates/stwo-p256/src/components/fake_glv/ec_source/air.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/ec_source/prepared_point_source.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/prepared_table/interaction.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/selector/direct_operand.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/selector/signed_operand.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/selector/lsb_correction.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/chain/expansion.rs`
- Modify: `crates/stwo-p256/src/components/fake_glv/chain/continuity.rs`

- [ ] **Step 1: Replace provider/consumer pairs with component-sum claims**

For operand/source structs currently shaped as:

```rust
pub struct XInteractionClaim {
    pub provider_claimed_sum: SecureField,
    pub consumer_claimed_sum: SecureField,
}
```

replace with:

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XInteractionClaim {
    pub claimed_sum: SecureField,
}
```

Set `claimed_sum` to the `logup.finalize_last()` result for that component.

- [ ] **Step 2: Split multi-component chain claims**

For `FakeGlvChainExpansionInteractionClaim`, replace:

```rust
pub expansion_claimed_sum: SecureField,
pub primitive_claimed_sum: SecureField,
```

with:

```rust
pub expansion: ComponentInteractionClaim,
pub primitive: ComponentInteractionClaim,
```

where:

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentInteractionClaim {
    pub claimed_sum: SecureField,
}
```

- [ ] **Step 3: Normalize prepared-table pinned claim**

Replace direct semantic fields in `PreparedTableEcRowPinnedInteractionClaim`:

```rust
total_claimed_sum
prepared_table_provider_claimed_sum
cert_base_consumer_claimed_sum
canonical_claimed_sum
final_check_hint_claimed_sum
gamma_yield_sum
```

with component-named claims:

```rust
pub total: ComponentInteractionClaim,
pub prepared_table: ComponentInteractionClaim,
pub cert_base: ComponentInteractionClaim,
pub canonical: ComponentInteractionClaim,
pub final_check_hint: ComponentInteractionClaim,
pub gamma: ComponentInteractionClaim,
```

Each nested claim must contain only `claimed_sum`.

- [ ] **Step 4: Run fake-GLV and prepared-table release tests**

Run:

```bash
rtk cargo test -p stwo-p256 --release fake_glv
rtk cargo test -p stwo-p256 --release prepared_table
```

Expected: component tests pass after proof-layer references are updated in Task 6.

---

### Task 5: Normalize Top-Level Proof Claims and Transcript Mixing

**Files:**
- Modify: `crates/stwo-p256/src/proof/mod.rs`
- Modify: `crates/stwo-p256/src/proof/balances.rs`

- [ ] **Step 1: Remove direct semantic `SecureField` fields from `P256CurrentAirInteractionClaim`**

Delete:

```rust
pub ecdsa_result_provider_claimed_sum: SecureField,
```

Any remaining direct `SecureField` field in `P256CurrentAirInteractionClaim` must be deleted or wrapped as a component `InteractionClaim`.

- [ ] **Step 2: Change `P256CurrentAirInteractionClaim::zero`**

Every field should be a component claim:

```rust
fake_glv_scalar_air: FakeGlvScalarAirInteractionClaim::zero(),
final_check: FinalCheckAirInteractionClaim::zero(),
```

No line in this constructor should assign a raw `SecureField` semantic balance.

- [ ] **Step 3: Change `mix_into` to flatten component claims only**

Remove direct calls like:

```rust
channel.mix_felts(&[self.ecdsa_result_provider_claimed_sum]);
```

Use only:

```rust
self.public_inputs.mix_into(channel);
self.scalar_setup.mix_into(channel);
self.cert_scalar_inputs.mix_into(channel);
self.fake_glv_scalar_air.mix_into(channel);
```

and equivalent calls for every component field in deterministic proof order.

- [ ] **Step 4: Remove legacy balance proof structs**

If `P256ProofInteractionClaim` and `RelationBalanceClaim` in `crates/stwo-p256/src/proof/balances.rs` are still verifier-facing, delete them. If tests use them as diagnostics, move them behind `#[cfg(test)]` and rename them to:

```rust
DebugRelationBalance
DebugRelationAudit
```

---

### Task 6: Replace Verifier-Facing Relation Balances With Recomputed Debug Audits

**Files:**
- Modify: `crates/stwo-p256/src/proof/mod.rs`
- Modify: `crates/stwo-p256/src/proof/tests.rs`
- Modify: component-local tests that mutate removed side fields

- [ ] **Step 1: Delete proof verification dependence on side fields**

Remove `relation_balances()` entries that depend on removed prover-supplied semantic fields, including:

```rust
"FakeGlvScalarTotalConsistency"
"HintedMulTotalConsistency"
"PreparedTablePinnedConsistency"
"PreparedTablePinnedBreakdown"
```

Keep only balances that are verifier-recomputed from public data or component claimed sums.

- [ ] **Step 2: Move relation audit to test-only recomputation**

Keep an audit function only under `#[cfg(test)]`:

```rust
#[cfg(test)]
fn relation_audit_from_trace_and_instances(&self) -> RelationAudit {
    RelationAudit {
        balances: self.debug_relation_balances_from_trace_and_instances(),
        liveness: self.liveness_witnesses(),
    }
}
```

The debug audit must not read fields from proof interaction claims that a prover can choose independently.

- [ ] **Step 3: Update mutation tests**

Replace tests that mutate removed side fields with tests that mutate:

```rust
interaction_claim.some_component.claimed_sum += SecureField::one();
```

or mutate committed witness data before proving.

- [ ] **Step 4: Run proof-layer release tests**

Run:

```bash
rtk cargo test -p stwo-p256 --release proof::
```

Expected: proof tests pass or only known ignored tests remain ignored.

---

### Task 7: Enforce `Claim` and `ProofClaim` Shape Parity

**Files:**
- Modify: `crates/stwo-p256/src/proof/tests.rs`
- Modify: all component files with `*ProofClaim` structs listed by the guard failure

- [ ] **Step 1: Add claim-shape guard test**

Add:

```rust
#[test]
fn proof_claim_structs_do_not_contain_interaction_or_relation_sums() {
    let forbidden = [
        "claimed_sum: SecureField",
        "consumer_claimed_sum",
        "provider_claimed_sum",
        "total_claimed_sum",
        "yield_sum",
        "use_sum",
    ];
    let mut offenders = Vec::new();

    for path in stwo_p256_source_files() {
        let source = std::fs::read_to_string(&path).expect("source file is readable");
        if !(source.contains("ProofClaim") || source.contains("pub struct Claim")) {
            continue;
        }
        for (line_index, line) in source.lines().enumerate() {
            if forbidden.iter().any(|needle| line.contains(needle)) {
                offenders.push(format!(
                    "{}:{}: {}",
                    path.strip_prefix(env!("CARGO_MANIFEST_DIR"))
                        .unwrap_or(&path)
                        .display(),
                    line_index + 1,
                    line.trim()
                ));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "proof claims must carry shape/public data, not interaction sums:\n{}",
        offenders.join("\n")
    );
}
```

- [ ] **Step 2: Run test red**

Run:

```bash
rtk cargo test -p stwo-p256 --release proof_claim_structs_do_not_contain_interaction_or_relation_sums
```

Expected: fail until all `Claim`/`ProofClaim` structs carry only log sizes, schedules, public instances, and non-interaction proof shape data.

- [ ] **Step 3: Refactor failing structs**

For each offender, remove interaction sums from `Claim`/`ProofClaim`. Preserve legitimate shape fields such as:

```rust
pub log_size: u32,
pub log_sizes: Vec<u32>,
pub instances: Vec<PublicEcdsaInstance<M31>>,
```

Do not preserve any field whose value is a LogUp claimed sum.

---

### Task 8: Final Verification

**Files:**
- No new files.
- Validate all modified files.

- [ ] **Step 1: Run structural guards**

Run:

```bash
rtk cargo test -p stwo-p256 --release interaction_claim_structs_match_stwo_cairo_shape
rtk cargo test -p stwo-p256 --release top_level_interaction_claim_has_no_direct_semantic_secure_fields
rtk cargo test -p stwo-p256 --release proof_claim_structs_do_not_contain_interaction_or_relation_sums
```

Expected: all pass.

- [ ] **Step 2: Run component-focused release suites**

Run:

```bash
rtk cargo test -p stwo-p256 --release fake_glv
rtk cargo test -p stwo-p256 --release scalar_setup
rtk cargo test -p stwo-p256 --release final_add
rtk cargo test -p stwo-p256 --release hinted_mul
rtk cargo test -p stwo-p256 --release public_key_curve
```

Expected: all selected tests pass.

- [ ] **Step 3: Run full release suite**

Run:

```bash
rtk cargo test -p stwo-p256 --release
```

Expected: all non-ignored tests pass.

- [ ] **Step 4: Review diff for reference parity**

Run:

```bash
rtk git diff -- crates/stwo-p256/src
```

Expected: proof-facing struct shapes match `stwo-cairo`; no removed side sum has been reintroduced under a different public field name.

---

## Self-Review

Spec coverage: the plan covers all comparable stwo-cairo struct categories: component `Claim`, `ProofClaim`, `InteractionClaim`, component containers through constructor updates, top-level aggregate claims, transcript mixing, and relation-audit demotion.

Placeholder scan: no step relies on an unspecified future implementation; each task names files, target shapes, commands, and expected outcomes.

Type consistency: all normalized component interaction claims use `claimed_sum: SecureField`; aggregate claims contain nested component claims rather than semantic `SecureField` side sums.
