# The end goal — BD one-pager (2026-07)

## One sentence

We are building the engine that lets 450M Europeans prove things like "I'm
over 18" from their government-issued digital ID — on their phone, in under
a second — without revealing who they are, and without any government or
issuer having to change anything.

## The regulatory tailwind (why this market exists)

- **eIDAS 2.0 (Regulation EU 2024/1183, in force):** every EU Member State
  must offer citizens an EU Digital Identity Wallet. Recital 14 explicitly
  directs Member States to integrate **zero-knowledge proofs** so a relying
  party can validate a claim ("over 18", "EU resident") *without receiving
  the underlying identity data*.
- **The EU Commission has already specified the technology: TS13** — the
  official technical specification for ZKPs based on arithmetic circuits in
  the EUDI Wallet. It names one concrete proof system type,
  `longfellow-libzk-v1` (the Google/ISO approach), is being piloted in the
  **EU Age Verification app**, and is being handed to **ETSI (TS 119 476-2)**
  for formal standardization. This is not a research bet; it is the written
  compliance path.
- **Demand side:** the DSA and national age-assurance laws are forcing
  platforms (adult content, social media, gaming, alcohol delivery) to
  verify age NOW — and privacy regulators punish them if they over-collect.
  Age verification is the wedge use case the EU itself chose to pilot.

## What the product is

A production implementation of exactly what TS13 specifies: a prover +
verifier that takes a citizen's **existing** government mdoc credential
(ISO 18013-5 — the same format as mobile driver's licenses and the EU PID)
and produces a zero-knowledge presentation proving, cryptographically:

- the credential was **genuinely signed by the government issuer** (P-256,
  certificate chain to the trust list),
- it is **currently valid** (not expired),
- it is **bound to this holder's device** and **this session** (fresh
  nonce — a stolen or replayed proof is useless),
- and the **specific claim requested** — over-18, nationality in a set —
  is true,

while revealing **nothing else**: no name, no birth date, no document
number, no signature bytes, no correlation handle. Two presentations by the
same person are mathematically unlinkable.

## Why this approach wins (TS13's own arguments)

1. **Zero issuer changes.** Works on credentials governments already issue.
   No new signature schemes, no reissuance, no infrastructure migration —
   TS13 calls this "the biggest advantage of this approach." (The rival
   path, TS14/BBS+, requires issuers to adopt new cryptography.)
2. **No trusted setup.** Nothing to ceremony, nothing to compromise —
   soundness is statistical (100+ bits), a hard TS13 requirement.
3. **Mobile-fast.** The published bar (Google's libzk): ~800 ms proving on
   a Pixel 6, ~400 KB proof. Our engine is built to meet and beat that bar,
   in Rust — memory-safe, embeddable in wallet apps via FFI.
4. **Standards-aligned end to end:** the proof plugs into the official
   rails — ISO 18013-5 ZkDocument responses, OpenID4VP/DCQL requests,
   published circuit fingerprints a verifier can pin.

## Where we are and what "done" looks like

Today: the full statement (issuer signature + device binding + nonce +
validity + attribute predicates) already proves end-to-end in **~0.8 s**
in the transparent (non-hiding) configuration; the zero-knowledge
configuration is in final integration with a measured path from ~12 s to
the ~2 s target on the two known levers (encode swap, binding shrink) —
both designed, one landing now.

**Endgame:** the reference-grade, TS13-conformant `longfellow-libzk-v1`
engine — prove ≤1 s on mid-range phones, proof ~sub-MB, verification
trivially cheap, formally pinned circuits, revocation-ready — positioned
as the ZK layer that EUDI wallet vendors, age-verification providers, and
relying-party platforms integrate instead of building cryptography teams.
The standard is written, the pilot is live, the deadline is regulatory:
we're building the engine everyone will need to comply with it.
