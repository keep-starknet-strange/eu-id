#!/usr/bin/env bash
#
# G8 quantum-only dependency-tree gate (tasks/pq-clean-scheme-spec.md §3/§4).
#
# INVARIANT: the quantum-safe eu-id-prover build
# (`--no-default-features --features quantum-safe-mdoc`) carries no classical
# public-key crypto: none of the RustCrypto P-256/ECDSA stack (p256, ecdsa,
# elliptic-curve, primeorder, sec1, rfc6979) and none of our P-256 proving
# crates (stwo-p256, eu-id-ec-coprocessor) may appear as a normal dependency.
#
# Known engine-internal exception: the stwo STARK engine depends on
# starknet-crypto (felt/Poseidon utilities), which pulls `rfc6979` for its own
# Stark-curve module. That path is part of the proving engine, not our
# credential scheme's public-key crypto, and exists in EVERY build of stwo.
# The gate therefore allows `rfc6979` if and only if its sole inverse
# dependency is `starknet-crypto`; everything else on the pattern fails hard.
set -euo pipefail

cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

PATTERN='p256|ecdsa|elliptic-curve|primeorder|sec1|rfc6979|stwo-p256|stwo-p256-utils|eu-id-ec-coprocessor'
TREE_ARGS=(--locked --workspace -e normal)

echo "==> cargo tree ${TREE_ARGS[*]} | grep -E \"$PATTERN\""
if ! dependency_tree=$(cargo tree "${TREE_ARGS[@]}"); then
    echo "FAIL: unable to resolve the locked quantum workspace dependency tree"
    exit 1
fi
matches=$(echo "$dependency_tree" | grep -E "$PATTERN" | sed 's/[│├└─ ]*//' | sort -u || true)

if [[ -z "$matches" ]]; then
    echo "==> quantum-only dependency tree is clean"
    exit 0
fi

# Every match must be rfc6979, and rfc6979's only inverse dependency must be
# starknet-crypto (the stwo engine). Anything else is a classical-crypto leak.
non_rfc=$(echo "$matches" | grep -v '^rfc6979 ' || true)
if [[ -n "$non_rfc" ]]; then
    echo "FAIL: classical public-key crypto in the quantum-only tree:"
    echo "$non_rfc"
    exit 1
fi

rfc_parents=$(cargo tree "${TREE_ARGS[@]}" -i rfc6979 --depth 1 --prefix none | tail -n +2)
unexpected_rfc_parents=$(echo "$rfc_parents" | grep -v '^starknet-crypto ' || true)
if [[ -z "$rfc_parents" || -n "$unexpected_rfc_parents" ]]; then
    echo "FAIL: rfc6979 is reachable outside the stwo engine's starknet-crypto:"
    cargo tree "${TREE_ARGS[@]}" -i rfc6979 --depth 1
    exit 1
fi

echo "==> quantum-only dependency tree is clean"
echo "    (rfc6979 present only via the stwo engine's starknet-crypto — allowed)"
