#!/usr/bin/env python3
"""Generate the Phase V PID mdoc test vector using the EU reference issuer.

Issues a genuine `eu.europa.ec.eudi.pid.1` mdoc with pyMDOC-CBOR
(github.com/eu-digital-identity-wallet/pyMDOC-CBOR, Apache-2.0) so the vector
comes from an independent third-party encoder rather than our own parser.

Outputs (into crates/eu-id-prover/tests/vectors/pid_pymdoc_v1/):
  issuer_signed.cbor  frozen IssuerSigned bytes (nameSpaces + issuerAuth)
  issuer_chain.der    DS (leaf) certificate, DER; chains to the test IACA root
  device_key.pem      test-only device P-256 PRIVATE key (PEM, PKCS#8)
  README.md           attribution, pinned commit, generation command, determinism

Determinism: pyMDOC-CBOR shuffles the attribute map (shuffle_dict) and draws
per-item salts from secrets.token_bytes, so the output bytes are NOT
reproducible run-to-run. The issuer, IACA/DS keypairs and the device keypair
are all derived from fixed seeds here, but the *vendored output bytes* are the
frozen artifact; this script is documentation + reproducer of the process, not
a byte-exact reproducer. (Verified fact per Q-002.)

Usage:
  python tools/gen_pid_vector.py <output_dir>
"""
import sys
import base64
from pathlib import Path

from cryptography import x509
from cryptography.x509.oid import NameOID, ExtendedKeyUsageOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec

from pymdoccbor.mdoc.issuer import MdocCborIssuer

# --- fixed identifiers (frozen by Q-002) --------------------------------------
DOCTYPE = "eu.europa.ec.eudi.pid.1"        # NOTE: eudi, NOT the README's old eudiw
NAMESPACE = "eu.europa.ec.eudi.pid.1"

PID_ATTRS = {
    "family_name": "Mustermann",
    "given_name": "Erika",
    "birth_date": "1985-05-05",
    "nationality": "DE",
    "issuance_date": "2026-01-01",
    "expiry_date": "2030-01-01",
}

import datetime
VALIDITY = {
    "issuance_date": datetime.datetime(2026, 1, 1, 0, 0, 0),
    "expiry_date": datetime.datetime(2030, 1, 1, 0, 0, 0),
}

# --- fixed test seeds (test-only, never production) ---------------------------
# EC private scalars are derived deterministically from these seeds so the
# IACA root, DS (issuer) key and device key are stable across runs.
IACA_SEED = bytes.fromhex("11" * 32)
DS_SEED = bytes.fromhex("22" * 32)
DEVICE_SEED = bytes.fromhex("33" * 32)

P256_ORDER = int(
    "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16
)


def ec_key_from_seed(seed: bytes) -> ec.EllipticCurvePrivateKey:
    """Deterministic P-256 private key from a 32-byte seed (test-only)."""
    d = (int.from_bytes(seed, "big") % (P256_ORDER - 1)) + 1
    return ec.derive_private_key(d, ec.SECP256R1())


def build_iaca_root(key: ec.EllipticCurvePrivateKey) -> x509.Certificate:
    name = x509.Name([
        x509.NameAttribute(NameOID.COUNTRY_NAME, "DE"),
        x509.NameAttribute(NameOID.ORGANIZATION_NAME, "EU Wallet Test IACA"),
        x509.NameAttribute(NameOID.COMMON_NAME, "EU Wallet Test IACA Root"),
    ])
    return (
        x509.CertificateBuilder()
        .subject_name(name)
        .issuer_name(name)
        .public_key(key.public_key())
        .serial_number(0x1ACA)
        .not_valid_before(datetime.datetime(2025, 1, 1))
        .not_valid_after(datetime.datetime(2035, 1, 1))
        .add_extension(x509.BasicConstraints(ca=True, path_length=0), critical=True)
        .add_extension(
            x509.KeyUsage(
                digital_signature=False, content_commitment=False,
                key_encipherment=False, data_encipherment=False,
                key_agreement=False, key_cert_sign=True, crl_sign=True,
                encipher_only=False, decipher_only=False,
            ),
            critical=True,
        )
        .sign(key, hashes.SHA256())
    )


def build_ds_cert(
    ds_key: ec.EllipticCurvePrivateKey,
    iaca_key: ec.EllipticCurvePrivateKey,
    iaca_cert: x509.Certificate,
) -> x509.Certificate:
    subject = x509.Name([
        x509.NameAttribute(NameOID.COUNTRY_NAME, "DE"),
        x509.NameAttribute(NameOID.ORGANIZATION_NAME, "EU Wallet Test DS"),
        x509.NameAttribute(NameOID.COMMON_NAME, "EU Wallet Test Document Signer"),
    ])
    return (
        x509.CertificateBuilder()
        .subject_name(subject)
        .issuer_name(iaca_cert.subject)
        .public_key(ds_key.public_key())
        .serial_number(0x005)
        .not_valid_before(datetime.datetime(2025, 1, 1))
        .not_valid_after(datetime.datetime(2032, 1, 1))
        .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
        .add_extension(
            x509.KeyUsage(
                digital_signature=True, content_commitment=False,
                key_encipherment=False, data_encipherment=False,
                key_agreement=False, key_cert_sign=False, crl_sign=False,
                encipher_only=False, decipher_only=False,
            ),
            critical=True,
        )
        .add_extension(
            x509.ExtendedKeyUsage([x509.ObjectIdentifier("1.0.18013.5.1.2")]),
            critical=False,
        )
        .sign(iaca_key, hashes.SHA256())
    )


def cose_privkey_dict(key: ec.EllipticCurvePrivateKey) -> dict:
    nums = key.private_numbers()
    return {
        "KTY": "EC2",
        "CURVE": "P_256",
        "ALG": "ES256",
        "D": nums.private_value.to_bytes(32, "big"),
        "KID": b"test-ds-kid",
    }


def main(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)

    iaca_key = ec_key_from_seed(IACA_SEED)
    ds_key = ec_key_from_seed(DS_SEED)
    device_key = ec_key_from_seed(DEVICE_SEED)

    iaca_cert = build_iaca_root(iaca_key)
    ds_cert = build_ds_cert(ds_key, iaca_key, iaca_cert)

    # DS cert is what pyMDOC embeds in issuerAuth's x5chain (label 33). Write it
    # to a temp file so the issuer picks up exactly these bytes.
    ds_der = ds_cert.public_bytes(serialization.Encoding.DER)
    ds_der_path = out_dir / "_ds_cert.der"
    ds_der_path.write_bytes(ds_der)

    # Device public key handed to the issuer as a base64url-encoded PEM string,
    # which the issuer route in issuer.new() converts to a COSE_Key.
    device_pub_pem = device_key.public_key().public_bytes(
        serialization.Encoding.PEM,
        serialization.PublicFormat.SubjectPublicKeyInfo,
    )
    device_pub_b64url = base64.urlsafe_b64encode(device_pub_pem).decode("ascii")

    issuer = MdocCborIssuer(
        private_key=cose_privkey_dict(ds_key),
        alg="ES256",
    )
    issuer.new(
        doctype=DOCTYPE,
        data={NAMESPACE: dict(PID_ATTRS)},
        validity=VALIDITY,
        devicekeyinfo=device_pub_b64url,
        cert_path=str(ds_der_path),
    )

    issuer_signed_bytes = issuer.dump()  # cbor2.dumps(self.signed, canonical=True)

    (out_dir / "issuer_signed.cbor").write_bytes(issuer_signed_bytes)

    # Chain file: DS leaf then IACA root, concatenated DER (leaf-first).
    iaca_der = iaca_cert.public_bytes(serialization.Encoding.DER)
    (out_dir / "issuer_chain.der").write_bytes(ds_der + iaca_der)

    device_priv_pem = device_key.private_bytes(
        serialization.Encoding.PEM,
        serialization.PrivateFormat.PKCS8,
        serialization.NoEncryption(),
    )
    (out_dir / "device_key.pem").write_bytes(device_priv_pem)

    ds_der_path.unlink()  # temp

    print(f"wrote issuer_signed.cbor ({len(issuer_signed_bytes)} bytes)")
    print(f"wrote issuer_chain.der  ({len(ds_der) + len(iaca_der)} bytes)")
    print(f"wrote device_key.pem    ({len(device_priv_pem)} bytes)")


if __name__ == "__main__":
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(
        "crates/eu-id-prover/tests/vectors/pid_pymdoc_v1"
    )
    main(out)
