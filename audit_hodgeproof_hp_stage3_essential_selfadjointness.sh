#!/usr/bin/env bash
set -euo pipefail

report=stage3_essential_selfadjointness_audit.txt
mathlib=.lake/packages/mathlib/Mathlib

search() {
  local status=0
  rg -n -i "$@" || status=$?
  if [ "$status" -gt 1 ]; then
    exit "$status"
  fi
}

{
  echo '=== Hermite completeness and basis tools ==='
  search \
    -e 'hermite.*(basis|complete|dense|orthonormal)' \
    -e '(basis|complete|dense|orthonormal).*hermite' \
    "$mathlib/Analysis" \
    "$mathlib/RingTheory/Polynomial/Hermite"

  echo '=== Essential self-adjointness and deficiency tools ==='
  search \
    -e 'essentially.?self.?adjoint' \
    -e 'deficiency.?index' \
    -e 'self.?adjoint.*(surjective|dense.?range)' \
    -e '(surjective|dense.?range).*self.?adjoint' \
    "$mathlib/Analysis" \
    "$mathlib/Topology/Algebra/Module"

  echo '=== Current project declarations ==='
  search \
    -e 'theorem hpHarmonicClosure_le_core_adjoint' \
    -e 'theorem hpHarmonicClosure_domain_dense' \
    -e 'theorem hpGaussianGroundL2_closure_eigenvector' \
    HodgeProofHP
} > "$report"

echo "Audit saved to $report"
cat "$report"
