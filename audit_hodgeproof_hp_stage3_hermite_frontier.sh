#!/usr/bin/env bash
set -euo pipefail

mathlib_dir=.lake/packages/mathlib/Mathlib
report=stage3_hermite_frontier_audit.txt

if [ ! -d "$mathlib_dir" ]; then
  echo "STOP: run this from the hodgeproof-hp repository root"
  exit 1
fi

{
  printf '%s\n' '=== Hermite declarations ==='
  rg -n -i --glob '*.lean' \
    '(theorem|lemma|def|instance).*hermite' \
    "$mathlib_dir/RingTheory/Polynomial/Hermite" \
    "$mathlib_dir/Analysis" || true

  printf '\n%s\n' '=== Gaussian and Schwartz declarations ==='
  rg -n -i --glob '*.lean' \
    '(theorem|lemma|def|instance).*(gaussian|schwartz)' \
    "$mathlib_dir/Analysis/SpecialFunctions/Gaussian" \
    "$mathlib_dir/Analysis/Distribution/SchwartzSpace" || true

  printf '\n%s\n' '=== Unbounded operator spectral tools ==='
  rg -n -i --glob '*.lean' \
    '(essentially.?self.?adjoint|deficiency|compact.resolvent|eigenvector.basis)' \
    "$mathlib_dir/Analysis/InnerProductSpace" \
    "$mathlib_dir/Topology/Algebra/Module" || true
} > "$report"

echo "Audit saved to $report"
rg -n '^(===|.*essentially.?self.?adjoint|.*deficiency|.*eigenvector.basis)' \
  "$report" | head -80 || true
