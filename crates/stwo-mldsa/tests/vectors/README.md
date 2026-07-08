# Vendored NIST ACVP ML-DSA-65 sigVer vectors

`mldsa65_sigver.json` is a filtered subset of the official NIST ACVP known-answer
tests for ML-DSA signature verification (FIPS 204).

## Provenance

- Source repo: <https://github.com/usnistgov/ACVP-Server>
- File: `gen-val/json-files/ML-DSA-sigVer-FIPS204/internalProjection.json`
- Commit: `15c0f3deeefbfa8cb6cd32a99e1ca3b738c66bf0` (master, 2026-04-16)
- ACVP `vsId` 42, algorithm `ML-DSA`, revision `FIPS204`.

## What was kept

The upstream `internalProjection.json` (~4.5 MB) covers ML-DSA-44/65/87 across
several signature interfaces (external/internal, pure/preHash, externalMu). Our
M1 reference implements **Algorithm 3 (`ML-DSA.Verify`) in pure mode over the
external interface**, so we vendor exactly the matching group:

- `parameterSet = ML-DSA-65`
- `testGroup 3`: `signatureInterface = external`, `preHash = pure`,
  `externalMu = false`

That group has **15 cases: 3 valid + 12 invalid** (the invalid cases mutate the
signature `z`, the commitment `c̃`, the hint `h`, or the message). Each case
carries its own `pk`, `message`, `context`, `signature`, `testPassed`, and
`reason`. The vendored file is ~313 KB (well under the 2 MB budget); the fields
irrelevant to verification (`sk`, `deferred`, `hashAlg`) were dropped.

## Regenerating

```sh
curl -sL "https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/json-files/ML-DSA-sigVer-FIPS204/internalProjection.json" -o ip.json
# then filter parameterSet==ML-DSA-65 && tgId==3, projecting
# {tcId, pk, message, context, signature, testPassed, reason}.
```

Consumed by `crates/stwo-mldsa/tests/kats.rs`.
