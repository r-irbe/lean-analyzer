#!/usr/bin/env bash
# Regenerate tests/fixtures/lean_oracle.tsv using the pinned Lean 4 toolchain.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${CRATE_DIR}/lean"
lake env lean --run "${SCRIPT_DIR}/gen_oracle.lean" > "${CRATE_DIR}/tests/fixtures/lean_oracle.tsv"
echo "Regenerated ${CRATE_DIR}/tests/fixtures/lean_oracle.tsv"
