#!/usr/bin/env bash
# Build generated certificate batches sequentially to avoid launching all 80
# Lean processes together. Proofs and pinned resource settings are unchanged.
set -euo pipefail
cd "$(dirname "$0")/.."
shopt -s nullglob
batches=(HodgeProofHP/Stage5ThetaJensenCellsBatch[0-9][0-9][0-9].lean)
if (( ${#batches[@]} != 80 )); then
  echo "Expected 80 Stage 5 certificate batches; found ${#batches[@]}" >&2
  exit 1
fi
for source in "${batches[@]}"; do
  module="${source%.lean}"
  module="${module//\//.}"
  echo "Building certificate batch: $module"
  lake build "$module"
done
