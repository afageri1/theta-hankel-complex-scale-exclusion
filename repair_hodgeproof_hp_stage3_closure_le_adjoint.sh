#!/usr/bin/env bash
set -euo pipefail

for file in \
  HodgeProofHP/Stage3ClosureLeAdjoint.lean \
  create_hodgeproof_hp_stage3_closure_le_adjoint.sh
do
  if rg -q '^    HPHarmonicCoreOperator\.graph$' "$file"; then
    echo "ALREADY UPDATED: $file"
  elif rg -q '^  exact Submodule\.topologicalClosure_minimal$' "$file"; then
    sed -i \
      '/^  exact Submodule\.topologicalClosure_minimal$/a\    HPHarmonicCoreOperator.graph' \
      "$file"
    echo "UPDATED: $file"
  else
    echo "STOP: expected proof line not found in $file" >&2
    exit 1
  fi
done

lake env lean HodgeProofHP/Stage3ClosureLeAdjoint.lean
lake build HodgeProofHP.Stage3ClosureLeAdjoint
