#!/usr/bin/env python3
"""Precondition checks for the Phase V PID mdoc vector (Q-002 Step 2).

Asserts, against the vendored bytes only (no re-encoding by our code):
  - MSO digestAlgorithm == "SHA-256"
  - issuerAuth protected header == A1 01 26 (ES256)
  - issuerAuth unprotected header carries x5chain (label 33)
  - every IssuerSignedItem `random` salt is >= 16 bytes
  - birth_date elementValue is tstr or tag-1004-wrapped tstr "1985-05-05";
    reports the encoding and the 10-char text-date value_offset within the
    IssuerSignedItemBytes
  - nationality elementValue is the 2-char tstr "DE"
  - the issuer ECDSA signature verifies over the reconstructed COSE Sig_structure
    ("Signature1"), against the DS cert public key in the x5chain

Exit 0 = all PASS, exit 1 = at least one FAIL. Prints PASS/FAIL per check.

Usage: python tools/check_pid_vector.py <vector_dir>
"""
import sys
from pathlib import Path

import cbor2
from cryptography import x509
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import encode_dss_signature
from cryptography.exceptions import InvalidSignature

NAMESPACE = "eu.europa.ec.eudi.pid.1"
X5CHAIN_LABEL = 33
COSE_TAG_ENCODED_CBOR = 24
CBOR_TAG_FULL_DATE = 1004
ES256_PHDR = bytes.fromhex("a10126")
MIN_SALT_LEN = 16

results = []


def check(name, ok, detail=""):
    results.append((name, ok, detail))
    print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"  [{detail}]" if detail else ""))
    return ok


def hexdump(b):
    return b.hex()


def main(vec_dir: Path) -> int:
    raw = (vec_dir / "issuer_signed.cbor").read_bytes()
    issuer_signed = cbor2.loads(raw)

    issuer_auth = issuer_signed["issuerAuth"]  # [phdr_bstr, uhdr, payload_bstr, sig]
    phdr_bstr, uhdr, payload_bstr, signature = issuer_auth

    # --- protected header ----------------------------------------------------
    check(
        "issuerAuth protected header == A1 01 26 (ES256)",
        bytes(phdr_bstr) == ES256_PHDR,
        f"got {hexdump(bytes(phdr_bstr))}",
    )

    # --- x5chain -------------------------------------------------------------
    has_x5c = X5CHAIN_LABEL in uhdr
    check("x5chain (label 33) present in unprotected header", has_x5c,
          f"uhdr labels {list(uhdr.keys())}")

    # --- MSO payload ---------------------------------------------------------
    # payload is CBORTag(24, bstr(MSO)); MSO is the actual map
    payload_tagged = cbor2.loads(payload_bstr)
    mso_bytes = payload_tagged.value if isinstance(payload_tagged, cbor2.CBORTag) else payload_bstr
    mso = cbor2.loads(mso_bytes)

    check(
        'MSO digestAlgorithm == "SHA-256"',
        mso.get("digestAlgorithm") == "SHA-256",
        f'got {mso.get("digestAlgorithm")!r}',
    )

    # --- IssuerSignedItems: salts, birth_date, nationality -------------------
    items = issuer_signed["nameSpaces"][NAMESPACE]
    by_id = {}
    salt_ok = True
    min_salt = None
    for it in items:
        # it is CBORTag(24, bstr(IssuerSignedItem))
        item_bytes = it.value
        inner = cbor2.loads(item_bytes)
        salt = inner["random"]
        min_salt = len(salt) if min_salt is None else min(min_salt, len(salt))
        if len(salt) < MIN_SALT_LEN:
            salt_ok = False
        by_id[inner["elementIdentifier"]] = (inner, item_bytes)

    check(f"all IssuerSignedItem salts >= {MIN_SALT_LEN} bytes", salt_ok,
          f"min salt len {min_salt}")

    # birth_date
    bd_inner, bd_item_bytes = by_id["birth_date"]
    bd_val = bd_inner["elementValue"]
    if isinstance(bd_val, cbor2.CBORTag) and bd_val.tag == CBOR_TAG_FULL_DATE:
        encoding = "tag-1004 tstr"
        date_str = bd_val.value
    elif isinstance(bd_val, str):
        encoding = "plain tstr"
        date_str = bd_val
    else:
        encoding = f"UNEXPECTED {type(bd_val).__name__}"
        date_str = None
    bd_ok = date_str == "1985-05-05"

    # value_offset: byte offset of the 10 date chars within IssuerSignedItemBytes.
    # The tstr head for a 10-char string is 0x6A; find the date payload directly.
    date_bytes = b"1985-05-05"
    value_offset = bd_item_bytes.find(date_bytes) if date_str else -1
    check(
        'birth_date elementValue == "1985-05-05"',
        bd_ok,
        f"encoding={encoding}, value_offset={value_offset}",
    )

    # nationality
    nat_inner, _ = by_id["nationality"]
    nat_val = nat_inner["elementValue"]
    check(
        'nationality elementValue == 2-char tstr "DE"',
        isinstance(nat_val, str) and nat_val == "DE" and len(nat_val) == 2,
        f"got {nat_val!r} ({type(nat_val).__name__})",
    )

    # --- issuer ECDSA signature over reconstructed Sig_structure -------------
    # COSE Sign1 Sig_structure = ["Signature1", body_protected, external_aad, payload]
    sig_structure = ["Signature1", bytes(phdr_bstr), b"", bytes(payload_bstr)]
    tbs = cbor2.dumps(sig_structure, canonical=True)

    ds_der = uhdr[X5CHAIN_LABEL]
    if isinstance(ds_der, list):
        ds_der = ds_der[0]
    ds_cert = x509.load_der_x509_certificate(bytes(ds_der))
    pub = ds_cert.public_key()

    # COSE ES256 signature is raw r||s (64 bytes); convert to DER for cryptography.
    r = int.from_bytes(signature[:32], "big")
    s = int.from_bytes(signature[32:], "big")
    der_sig = encode_dss_signature(r, s)
    sig_ok = True
    try:
        pub.verify(der_sig, tbs, ec.ECDSA(hashes.SHA256()))
    except InvalidSignature:
        sig_ok = False
    check("issuer ECDSA signature verifies over Sig_structure", sig_ok,
          f"sig_len={len(signature)}")

    # --- summary -------------------------------------------------------------
    failed = [(n, d) for n, ok, d in results if not ok]
    print()
    if failed:
        print(f"{len(failed)} FAILED")
        # Offending raw hex for the orchestrator STOP report
        print("issuerAuth[0] (phdr) hex:", hexdump(bytes(phdr_bstr)))
        return 1
    print("ALL PRECONDITIONS PASS")
    print(f"birth_date: encoding={encoding}, value_offset={value_offset}")
    return 0


if __name__ == "__main__":
    d = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(
        "crates/eu-id-prover/tests/vectors/pid_pymdoc_v1"
    )
    sys.exit(main(d))
