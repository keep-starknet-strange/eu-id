#!/usr/bin/env python3
"""Generate or check the classical product profile source manifests."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


PROFILE_ID = "eudi-pid-p256-identity"
SOURCE_ROOTS = (
    "crates/air-core/src",
    "crates/eu-id-ec-coprocessor/src",
    "crates/eu-id-prover/src",
    "crates/predicates/src",
    "crates/sdk/src",
    "crates/stwo-p256-utils/src",
    "crates/stwo-p256/src",
    "crates/stwo-sha256/src",
)
SOURCE_FILES = (
    "Cargo.lock",
    "Cargo.toml",
    "rust-toolchain.toml",
    "scripts/product_profile_artifacts.py",
    "crates/air-core/Cargo.toml",
    "crates/eu-id-ec-coprocessor/Cargo.toml",
    "crates/eu-id-prover/Cargo.toml",
    "crates/predicates/Cargo.toml",
    "crates/sdk/Cargo.toml",
    "crates/stwo-p256-utils/Cargo.toml",
    "crates/stwo-p256/Cargo.toml",
    "crates/stwo-sha256/Cargo.toml",
)
ARTIFACT_DIR = "artifacts/product-p256-identity"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def source_files(workspace: Path) -> list[dict[str, str]]:
    paths = {workspace / path for path in SOURCE_FILES}
    for root in SOURCE_ROOTS:
        paths.update((workspace / root).rglob("*.rs"))
    return [
        {
            "path": path.relative_to(workspace).as_posix(),
            "sha256": sha256(path.read_bytes()),
        }
        for path in sorted(paths)
    ]


def outputs(workspace: Path) -> dict[str, bytes]:
    sources = source_files(workspace)
    root_policy = canonical_json(
        {
            "format": "eudi-root-policy-source-manifest-v1",
            "policy": "verifier-reconstructs-canonical-tree0-from-bounded-public-statement",
            "profile_id": PROFILE_ID,
            "source_files": sources,
        }
    )
    profile = canonical_json(
        {
            "cargo_features": [],
            "format": "eudi-product-circuit-source-manifest-v1",
            "pcs": {
                "fold_step": 3,
                "log_blowup_factor": 2,
                "pow_bits": 20,
                "queries": 54,
            },
            "product_bounds": {
                "item_cbor_log_size": 11,
                "item_digest_log_size": 9,
                "max_attributes": 2,
                "max_cbor_log_size": 13,
                "max_issuer_sig_structure_bytes": 6164,
                "max_mso_payload_bytes": 6144,
                "max_packed_sha_messages": 5,
                "max_selected_item_bytes": 1024,
                "max_scope_log_size": 15,
                "packed_sha_message_order": [
                    "issuer_sig_structure",
                    "mso",
                    "revocation",
                    "selected_item_0",
                    "selected_item_1_if_and",
                ],
                "sha_log_n_rows": 14,
                "predicate": "modes=age,nat,and;values=private-birth-date,private-alpha2-nationality",
                "revocation": "mandatory-ts13-sorted-pair-p256",
            },
            "profile_id": PROFILE_ID,
            "root_policy_manifest_sha256": sha256(root_policy),
            "source_files": sources,
        }
    )
    return {
        "profile-manifest.json": profile,
        "root-policy-manifest.json": root_policy,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    workspace = Path(__file__).resolve().parents[1]
    artifact_dir = workspace / ARTIFACT_DIR
    generated = outputs(workspace)

    if args.check:
        expected_names = set(generated)
        actual_names = {
            path.relative_to(artifact_dir).as_posix()
            for path in artifact_dir.rglob("*")
            if path.is_file()
        }
        drift = [
            name
            for name, data in generated.items()
            if not (artifact_dir / name).is_file()
            or (artifact_dir / name).read_bytes() != data
        ]
        drift.extend(sorted(actual_names - expected_names))
        if drift:
            parser.error("artifact drift: " + ", ".join(drift))
        return 0

    artifact_dir.mkdir(parents=True, exist_ok=True)
    for name, data in generated.items():
        (artifact_dir / name).write_bytes(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
