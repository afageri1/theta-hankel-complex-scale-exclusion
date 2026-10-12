#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
generated=$(mktemp -d)
trap 'rm -rf "$generated"' EXIT
python scripts/generate_stage7_cubic_finite_integrals.py --output-dir "$generated"
for p in 90 55 42 15; do
  module="Stage7ThetaJensenCubicFiniteIntegralNeg${p}"
  cmp "$generated/${module}.lean" "HodgeProofHP/${module}.lean"
  LOG="stage7-jensen-cubic-finite-integral-neg${p}-axioms.log"
  lake build "HodgeProofHP.${module}"
  lake env lean "HodgeProofHP/${module}.lean" 2>&1 | tee "$LOG"
  python scripts/check_axioms.py "$LOG" \
    --expect "HodgeProofHP.hpThetaJensenCubicNeg${p}_batchIntegral_rectangle_bounds" \
    --expect "HodgeProofHP.hpThetaJensenCubicNeg${p}_batchIntegral_sum" \
    --expect "HodgeProofHP.hpThetaJensenCubicNeg${p}_finiteIntegral_bounds"
done
echo "PASS: all four finite cubic integrals; all dependencies allowed"
