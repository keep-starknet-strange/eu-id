#!/usr/bin/env bash
#
# Configure Git to use the version-controlled hooks in `.githooks`.
# The pre-commit hook runs the lint check before each commit.
#
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
git config core.hooksPath .githooks

echo "pre-commit hook enabled (core.hooksPath -> .githooks)"
echo "bypass it for a single commit with: git commit --no-verify"
