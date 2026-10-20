#!/usr/bin/env bash
# Build lean_analyzer.wasm (wasm32-unknown-unknown) and sync to downstream consumers.
# Strict 7-bit ASCII only (INV-001).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${CRATE_DIR}"
cargo build --target wasm32-unknown-unknown --release

WASM_OUT="${CRATE_DIR}/target/wasm32-unknown-unknown/release/lean_analyzer.wasm"
if [[ ! -f "${WASM_OUT}" ]]; then
  echo "ERROR: WASM binary not found at ${WASM_OUT}" >&2
  exit 1
fi

mkdir -p "${CRATE_DIR}/data"
cp "${WASM_OUT}" "${CRATE_DIR}/data/lean_analyzer.wasm"
echo "Synced ${CRATE_DIR}/data/lean_analyzer.wasm"

# Sync to monorepo consumers if present
REPO_ROOT="$(cd "${CRATE_DIR}/../.." 2>/dev/null && pwd || true)"
for dest in \
  "${REPO_ROOT}/src/wasm/lean_analyzer.wasm" \
  "${REPO_ROOT}/packages/lean-analysis/data/lean_analyzer.wasm" \
  "${REPO_ROOT}/docs/easci/lean/skills/tools/lean-lsp-mcp/data/lean_analyzer.wasm" \
  "/home/radu/code/lean-lsp-mcp/data/lean_analyzer.wasm" \
  "/home/radu/code/proof-skills/tools/lean-lsp-mcp/data/lean_analyzer.wasm"; do
  if [[ -d "$(dirname "${dest}")" ]]; then
    cp "${WASM_OUT}" "${dest}"
    echo "Synced ${dest}"
  fi
done
