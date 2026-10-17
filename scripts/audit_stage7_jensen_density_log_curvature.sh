#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-log-curvature-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityLogCurvature
lake env lean HodgeProofHP/Stage7ThetaJensenDensityLogCurvature.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiDensityNormalizedSlope_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_pos \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_deriv \
  --expect HodgeProofHP.hpThetaPhiSquareDensityLogSlope_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_deriv_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_secondDeriv \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_secondDeriv_neg_iff \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_strictConcaveOn_of_curvature
echo "PASS: actual square-variable density logarithmic derivatives and exact curvature criterion"
echo "PASS: density log concavity is conditional on the explicit density curvature sign"
echo "Global density curvature positivity and the higher-moment bridge remain unproved"
echo "The certified square-variable tail curvature is a different condition"
