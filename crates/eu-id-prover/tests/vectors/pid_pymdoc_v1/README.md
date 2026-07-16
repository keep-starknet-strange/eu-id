# PID mdoc test vector — `pid_pymdoc_v1`

Genuine `eu.europa.ec.eudi.pid.1` PID mdoc issued by the EU reference
implementation's issuer, **pyMDOC-CBOR**, for the Phase V real-vector gate test
(`real_vector_pid_pymdoc_end_to_end`). The bytes come from an independent
third-party encoder maintained by the EU Digital Identity Wallet org, not from
our own parser/encoder — this is the point of the "no hand-crafted fake vector"
rule (Q-002).

## Attribution / license

- Source encoder: **pyMDOC-CBOR** — github.com/eu-digital-identity-wallet/pyMDOC-CBOR
- License: **Apache-2.0** (modifications © 2023 European Commission; original by IdentityPython)
- **Pinned commit: `aecbd8e929879a882c9c45e435211561c7f2d1bb`** (PyPI version 0.5.4)

## Attributes

docType and namespace are both `eu.europa.ec.eudi.pid.1` (NOTE: `eudi`, not the
older `eudiw` spelling used in the upstream README example). Namespace map:

| element         | value        | CBOR encoding      |
| --------------- | ------------ | ------------------ |
| `family_name`   | `Mustermann` | tstr               |
| `given_name`    | `Erika`      | tstr               |
| `birth_date`    | `1985-05-05` | tag-1004 tstr      |
| `nationality`   | `DE`         | 2-char tstr        |
| `issuance_date` | `2026-01-01` | tag-1004 tstr      |
| `expiry_date`   | `2030-01-01` | tag-1004 tstr      |

`validityInfo`: `signed`/`validFrom` = 2026-01-01, `validUntil` = 2030-01-01
(brackets the fixed test policy date 2026-07-01).

## Files

- `issuer_signed.cbor` — frozen `IssuerSigned` bytes: `{issuerAuth, nameSpaces}`,
  `cbor2.dumps(..., canonical=True)`. issuerAuth is a COSE_Sign1 (ES256,
  protected header `A1 01 26`, x5chain in unprotected label 33). 1771 bytes.
- `issuer_chain.der` — DS (leaf) cert then test IACA root, concatenated DER,
  leaf-first. The DS cert is the one embedded in issuerAuth's x5chain. 892 bytes.
- `device_key.pem` — test-only device P-256 **private** key (PKCS#8 PEM). The
  matching public key is bound in the MSO `deviceKeyInfo`. Used by the host-side
  deviceSigned builder (Step 3), never by production code. 241 bytes.

## Generation

```
python tools/gen_pid_vector.py crates/eu-id-prover/tests/vectors/pid_pymdoc_v1
```

(run inside a venv with `pip install
"git+https://github.com/eu-digital-identity-wallet/pyMDOC-CBOR.git@aecbd8e929879a882c9c45e435211561c7f2d1bb"
cryptography cbor2 cbor-diag`.)

The IACA root, DS (issuer) keypair and device keypair are derived from fixed
test seeds (`0x11..`, `0x22..`, `0x33..`) in `tools/gen_pid_vector.py`.

## Determinism note

**The output bytes are NOT byte-reproducible run-to-run.** pyMDOC-CBOR shuffles
the attribute map (`shuffle_dict`, hence random `digestID` ordering) and draws
each IssuerSignedItem salt from `secrets.token_bytes(32)`. All keypairs are
seed-fixed, but the salts and item ordering are internal randomness the tool
does not expose. Therefore **these vendored bytes are the frozen artifact**;
`gen_pid_vector.py` is documentation + a reproducer of the *process*, not a
byte-exact reproducer of *these files*. Re-running produces a different-but-valid
vector. The frozen files here are the ones the gate test consumes.

## Precondition verification

`tools/check_pid_vector.py <dir>` asserts (all PASS for these bytes):
digestAlgorithm `SHA-256`; protected header `A1 01 26`; x5chain label 33 present;
all salts ≥ 16 bytes (32 here); `birth_date` = tag-1004 tstr `1985-05-05`
(`value_offset` = 69 within IssuerSignedItemBytes); `nationality` = 2-char tstr
`DE`; and the issuer ECDSA signature verifies natively over the reconstructed
COSE `Sig_structure` against the DS cert public key.
