#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-weighted-tail-derivative-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenWeightedTailDerivative
lake env lean HodgeProofHP/Stage7ThetaJensenWeightedTailDerivative.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_eq_total_sub_integral \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_deriv \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_differentiableOn
echo "PASS: weighted tail derivative; CNV positivity remains unproved"
