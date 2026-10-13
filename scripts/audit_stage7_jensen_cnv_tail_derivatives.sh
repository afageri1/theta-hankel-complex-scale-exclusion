#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-tail-derivatives-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVTailDerivatives
lake env lean HodgeProofHP/Stage7ThetaJensenCNVTailDerivatives.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_deriv \
  --expect HodgeProofHP.hpThetaPhiCNVTailFirstDerivative_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiCNVTailFirstDerivative_deriv \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_deriv_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_secondDeriv
echo "PASS: first and second derivatives of actual CNV tail expression; CNV positivity remains unproved"
