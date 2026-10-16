#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-finite-integral-comparison-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVFiniteIntegralComparison
lake env lean HodgeProofHP/Stage7ThetaJensenCNVFiniteIntegralComparison.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNVLogTranslateDifference_hasDerivAt \
  --expect HodgeProofHP.hpThetaCNVLogTranslateDifference_strictAntiOn \
  --expect HodgeProofHP.hpThetaPhiSquareTail_additive_product_lt \
  --expect HodgeProofHP.hpThetaPhiSquareTail_weighted_shift_intervalIntegrable \
  --expect HodgeProofHP.hpThetaPhiSquareTail_weighted_integral_comparison \
  --expect HodgeProofHP.hpThetaPhiSquareTail_two_weighted_integrals_comparison
echo "PASS: strict additive-kernel determinant sign and finite weighted integral comparisons"
echo "Improper moment integrals, normalization and general Turan inequalities remain unproved"
