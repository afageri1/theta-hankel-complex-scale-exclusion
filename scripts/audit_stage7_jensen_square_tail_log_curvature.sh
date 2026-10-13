#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-square-tail-log-curvature-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenSquareTailLogCurvature
lake env lean HodgeProofHP/Stage7ThetaJensenSquareTailLogCurvature.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiSquareTailLogSlope_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_deriv_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_secondDeriv \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_secondDeriv_neg_iff_CNV
echo "PASS: exact log curvature and CNV sign equivalence; CNV positivity remains unproved"
