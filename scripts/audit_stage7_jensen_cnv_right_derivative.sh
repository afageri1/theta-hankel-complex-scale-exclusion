#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-right-derivative-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVRightDerivative
lake env lean HodgeProofHP/Stage7ThetaJensenCNVRightDerivative.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_hasDerivWithinAt_nonnegative \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_hasDerivWithinAt_zero \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_hasDerivWithinAt_nonnegative \
  --expect HodgeProofHP.hpThetaPhiCNVTailFirstDerivative_zero \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_hasDerivWithinAt_zero
echo "PASS: actual weighted tail and CNV right derivatives at zero; endpoint derivative positivity remains unproved"
