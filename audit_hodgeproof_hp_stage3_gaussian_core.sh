#!/usr/bin/env bash
set -euo pipefail

mathlib=.lake/packages/mathlib/Mathlib
report=stage3_gaussian_core_audit.txt

{
  printf '%s\n' '=== Gaussian as Schwartz map ==='
  rg -n -i --glob '*.lean' '(gaussian|exp.*sq|exp.*norm).*schwartz|schwartz.*(gaussian|exp)' "$mathlib" || true

  printf '\n%s\n' '=== Gaussian construction and decay ==='
  rg -n --glob '*.lean' '(HasTemperateGrowth|hasTemperateGrowth|toSchwartzMap|mk.*Schwartz|exp_neg)' \
    "$mathlib/Analysis/Distribution/SchwartzSpace" \
    "$mathlib/Analysis/SpecialFunctions/Gaussian" || true

  printf '\n%s\n' '=== Hermite differential equations and orthogonality ==='
  rg -n -i --glob '*.lean' '(hermite.*(deriv|orthog|eigen|basis)|(?:deriv|orthog|eigen|basis).*hermite)' \
    "$mathlib/RingTheory/Polynomial/Hermite" "$mathlib/Analysis" || true
} > "$report"

echo "Audit saved to $report"
wc -l "$report"
