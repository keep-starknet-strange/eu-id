# Full mdoc Implementation Plan — Longfellow functional parity

Goal: the mdoc proof path accepts **real ISO/IEC 18013-5 PID mdocs** (canonical CBOR,
text-form dates, x5chain issuers) and proves the full statement **without host-side
trust boundaries**, matching what longfellow-zk ships functionally: age + nationality
predicates, issuer ECDSA, device ECDSA, salted-digest membership, and device-key
origin — all bound in one STARK. Prereq reading: `tasks/mdoc-credential-format-spec.md`
(v1 profile, implemented), `crates/eu-id-prover/src/mdoc.rs` (isolated circuit),
`docs/mdoc-credential-format.md`.

**Non-goals (do NOT touch):** privacy upgrades (`r,s` and ZK masking stay as-is),
revocation, pseudonyms, SD-JWT, in-circuit x509 verification, the S4 coprocessor
track (keep P256-module coupling composition-level so BL6 can swap it later), the
11-byte POC path (it stays as the parity benchmark baseline).

**House rules:** one phase = one landing (tests green, fmt, clippy, slow proof test
in release). If a phase hits an undecidable design point, STOP and write a question
file to `tasks/mdoc-mailbox/` (create it) instead of guessing. Never weaken an
existing test. Prefix commands with `rtk`.

---

## Phase 0 — Bench truth (do first, small)
The parity numbers currently measure the POC monolith; longfellow's numbers are for
an mdoc proof. Add bench coverage for the mdoc circuit so every later phase has a
baseline.
- Add `mdoc_bench` rows to `crates/eu-id-prover/benches/` (mirror `identity_bench`):
  median prove/verify wall-clock + proof size for `prove_mdoc_circuit` /
  `verify_mdoc_circuit` on the v1 fixture.
- Add `eu_id_bench_mdoc` to `crates/eu-id-ffi` (mirror the identity bench fn).
- Extend `src/shape_dump.rs` to dump the mdoc circuit's per-module column/cell
  breakdown (12 modules) — this is the observability every later phase reports
  against.
- Record baseline + breakdown in `crates/eu-id-prover/benches/docs/perf-log.md`.
**Acceptance:** perf-log has the mdoc baseline row and cell breakdown; FFI builds.

## Phase 0b — SHA sizing waste (perf, do before the feature phases)
`prove_mdoc_circuit` pads all four SHA modules to `shared_sha_log = max(...)`
(mdoc.rs ~line 939). A real MSO makes the issuer `Sig_structure` ~1–1.5 KB
(≈ log 11 rows) while each item preimage is ~2 blocks (≈ log 7) — the max-padding
burns up to ~16× rows on three of the four instances. Fix before the feature
phases so their perf rows aren't measured on a known-wasteful shape:
- Preferred: per-instance `log_n_rows` (the static tables are already shared via
  air-core preprocessed dedup, so nothing forces equal sizes — verify, then drop
  the max). Fallback if relations genuinely require equal sizing: one SHA module
  proving all four messages (the `SHA_GROUP_WIDTH` grouping machinery), mailbox
  with the two options costed if neither is a day's work.
- While here: the device P256 uses `.with_preprocessed_namespace("mdoc/device")`,
  duplicating the hinted-mul schedule preprocessed columns. The main monolith's
  nonce P256 shares them with NO namespace and its release tests pass — verify the
  schedule preprocessed is witness-independent and drop the mdoc namespace (frees a
  duplicated column set), or document in the module why it cannot be shared.
**Acceptance:** perf-log row showing the delta vs the Phase 0 baseline; slow mdoc
proof still passes.

## Phase A — Multi-block SHA field exposure (unlocks everything else)
`crates/stwo-sha256/src/field_exposure.rs` gates all yields to `is_first_block`
(offset < 64 asserted at construction). Canonical CBOR ordering and MSO-interior
windows need exposure from arbitrary blocks.
- New constructor `FieldExposure::from_preimage_windows_multi(&[(field_id, abs_offset, len)])`:
  absolute preimage byte offsets; each window resolves to `(block_idx, word_idx,
  byte_in_word)`. A window MUST NOT straddle a 64-byte block boundary — assert at
  construction (callers re-align; CBOR gives no alignment guarantees, so a window
  that straddles is a fixture/profile error, not a runtime case to support).
- Gate each yield to its block: the trace has `is_first_block` (t=0) and
  `is_last_block` (t=63) boundary flags (`crates/stwo-sha256/src/trace.rs` module
  docs). Add a block-index selector usable in the exposure AIR — preferred: a
  preprocessed block-index column (the trace is already sized by `log_n_rows`,
  which is proof-carried); acceptable alternative: per-exposure one-hot selector
  columns constrained via the boundary flags. If neither fits the existing
  constraint idioms cleanly, mailbox with the two options costed.
- Keep the old constructor working (POC path uses it unchanged).
**Tests:** expose windows in block 0, 1, and 2 of a 3-block message and bind them via
the existing field relation (positive); tamper one exposed byte ⇒ LogUp imbalance
(negative); straddling window ⇒ construction panic (negative); existing exposure
tests untouched and green.

## Phase B — Text-form values in predicates
Real PIDs encode `birth_date` as full-date **tstr** `"YYYY-MM-DD"` and nationality
as alpha-2 tstr (`"DE"`). The circuit must consume these directly.
- **B1 (age):** new text-date binding mode in `crates/predicates/src/age/` alongside
  the packed mode: consume a 10-byte exposed window; constrain bytes 4 and 7 equal
  `0x2D` ('-'); constrain the 8 digit bytes `d − 0x30 ∈ [0, 9]` (reuse the existing
  range-check tables — do not add a new table for a 4-bit check); recompose
  `year = Σ (dᵢ−48)·10^k`, `month`, `day` (linear once digits are ranged) and feed
  the existing age evaluation unchanged. Semantic validity (month ≤ 12 etc.) is
  already the predicate's job — unchanged.
- **B2 (nationality):** redefine the circuit statement over **2-byte ASCII alpha-2
  codes**: the accepted-set preprocessed table stores `256·b₀ + b₁` of the ASCII
  bytes; the exposed 2-byte window binds directly. Drop the `numeric_country`
  mapping from the circuit path (keep it host-side for display only). `Policy`
  gains/changes to `accepted_nationalities_alpha2: Vec<[u8;2]>` for the mdoc path;
  the POC path keeps numeric.
**Tests:** age proves from a text-date fixture; digit-corruption (a letter in the
year) ⇒ reject; wrong separator ⇒ reject; alpha-2 membership positive + negative;
POC packed mode regression green.

## Phase C — Profile v2: canonical CBOR
Supersede the v1 ordering deviation now that A+B remove its reasons.
- `IssuerSignedItem` in **canonical (RFC 8949 core deterministic) key order**:
  `random, digestID, elementValue, elementIdentifier` (shortest-encoded-key-first).
  `elementValue` as tstr per B. Drop the v1 `from_extracted` checks that enforced
  packed-bytes-at-offset and window-in-block-0; replace with: window within ONE
  block (A's rule) and window bytes match the parsed value's text bytes.
- Regenerate fixtures canonically (fixture builder emits canonical order; keep one
  deliberately-misordered fixture ONLY if a test needs a rejection case — otherwise
  ordering is no longer enforced, canonical is just what real wallets emit).
- Bump profile: `docs/mdoc-credential-format.md` → v2 section; v1 packed-bytes form
  remains accepted (it is a valid CBOR bstr value) — do not break the v1 fixtures.
**Acceptance:** the slow mdoc proof passes on a canonical text-value fixture; v1
fixture still proves; parser tests green.

## Phase D — In-circuit MSO bindings (kill the host trust boundaries)
Today `birth_date_digest`, `nationality_digest`, and the device key are **public
inputs** validated host-side. Longfellow binds them in-circuit; so do we. All three
sub-items use Phase A exposure over the **issuer `Sig_structure` preimage** (the MSO
is embedded in it as the COSE payload, so its bytes are already hashed in-circuit).
Offsets are prover-supplied public inputs; the soundness argument to include in the
module docs: window *content* is pinned (D1) and the surrounding bytes are covered
by the issuer signature, so a mispointed offset must still exhibit issuer-signed
bytes with the pinned identifier — i.e. a second genuine attribute, not a forgery.
- **D1 — elementIdentifier pinning:** expose the identifier window of each item
  preimage (`"birth_date"` 10 B, `"nationality"` 11 B) and bind to the public
  constant bytes (public-digest-bind style, constants not statement values).
- **D2 — digest membership:** expose the 32-byte `valueDigests[ns][digestID]` entry
  window in the issuer preimage; require byte-equality with the item SHA module's
  digest via a shared LogUp relation (a `WindowDigestBind` replacing
  `PublicDigestBind`). The two digests **leave `MdocCircuitStatement`** (also fixes
  the digest-as-linkability-handle leak as a side effect).
- **D3 — device-key origin:** expose the two 32-byte `deviceKey` coordinate windows
  (COSE_Key `-2`/`-3` values) in the MSO region; new `pubkey_bind` component
  mirroring `digest_bind` (bytes ↔ `P256M31BigInt` limb recomposition) binding the
  device P256 module's `pub_x, pub_y`. The device key **leaves the public
  statement**; `verify_mdoc_circuit` stops comparing it host-side.
**Tests per sub-item:** positive proof; window pointed at a different (valid) offset
⇒ reject unless it is a genuine second instance; tampered exposed byte ⇒ LogUp
imbalance; statement no longer contains digests/device key (API assertion).
**Perf rule:** D1+D2+D3 introduce five tiny bind surfaces (2 identifier pins, 2
digest binds, 1 pubkey bind). Do NOT ship five log-4 dust components (the WO-3.2
component-dust lesson) — implement ONE multi-window bind component whose rows carry
(window kind, bytes, target relation), sized once.

## Phase E — ISO device auth + x5chain (host-side realism)
- **E1:** device signature payload = `DeviceAuthentication = ["DeviceAuthentication",
  SessionTranscript, docType, DeviceNameSpacesBytes]` (detached, built host-side on
  both sides from the verifier's own session transcript) instead of
  payload == raw transcript. `z_device` stays verifier-recomputable public.
- **E2:** accept `x5chain` (header 33) in issuerAuth unprotected headers: parse the
  leaf cert host-side (minimal DER walk or a small existing dep if one is already
  in-tree — check `Cargo.lock` first; do NOT add a heavy x509 stack without a
  mailbox), verify chain to a caller-supplied trusted root out-of-circuit, extract
  the leaf P-256 key as the issuer key. Keep bare `issuerKey` accepted for fixtures.
**Tests:** wrong session transcript ⇒ reject (existing, updated); x5chain fixture
extracts the right key; untrusted root ⇒ reject.

## Phase F — Promotion & retirement
- [x] Export the mdoc API as the product path: `eu_id_prover::{prove_mdoc, verify_mdoc}`
  (thin renames over the circuit fns), wire `crates/sdk` to it (replacing the
  POC+demo-nonce mapping), keep `prove_identity` (POC) untouched for benchmarks.
- [x] The nonce module is NOT part of the mdoc path (device auth subsumes it — and
  unlike the nonce, D3 proves key origin). It stays in the POC path only.
- [x] Final statement surface (document in `docs/mdoc-credential-format.md`): public =
  issuer key (or trusted root), policy, session transcript, `(r,s)` ×2, offsets;
  witness = everything else including digests and device key.
- [x] Update README status; perf-log row per phase landed (Phase 0 harness).
**Acceptance:** SDK end-to-end test proves+verifies a canonical v2 fixture through
the public API; full workspace tests green; perf-log shows the phase-by-phase cost.

---

## Performance budget & watch-items
- **Gate:** single-thread mdoc prove ≤ **2.0×** the POC monolith prove at every
  phase landing (the second P256 + issuer-sized SHA justify ~2×; more means waste).
  Any phase regressing its predecessor by > 10% ⇒ stop, mailbox with the shape-dump
  diff. Every phase adds a perf-log row (Phase 0 harness).
- **2×P256 is the accepted floor here** — do not optimize ECDSA duplication in this
  track; the S4-lite coprocessor (tasks/parity/s4/, ~28k quads/sig, batching via
  BL2 RLC) replaces both AIRs at BL6. Keep coupling composition-level so that swap
  stays mechanical.
- Static tables are shared across module instances by air-core preprocessed dedup
  (first-writer-wins by column ID) — SHA's log-16 tables and P256's log-18 tables
  are NOT duplicated. The per-instance costs that DO scale are trace rows (Phase 0b)
  and any namespaced preprocessed (Phase 0b).
- Exposure columns (Phase A) grow the SHA trace per exposed window — report the
  column delta in the Phase A perf row; if a canonical PID's window set pushes SHA
  wider than the shape budget, mailbox before landing.

## Order & dependencies
0 → 0b → A → {B, D} (both need A) → C (needs B) → E → F. B and D are
parallelizable. Estimated weight: A and D are the heavy ones (new AIR surface);
B medium; 0/0b/C/E/F light-medium. After every phase: the slow release-mode mdoc
proof test is the gate, plus the perf gate above.
