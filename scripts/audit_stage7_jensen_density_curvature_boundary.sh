#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-curvature-boundary-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityCurvatureBoundary
lake env lean HodgeProofHP/Stage7ThetaJensenDensityCurvatureBoundary.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_hasDerivAt \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_deriv \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_zero \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_hasDerivAt_zero \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_deriv_zero \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_div_tendsto_right \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_no_positive_linear_lower
echo "PASS: actual density curvature derivative expressed through the third kernel derivative"
echo "PASS: density curvature and its first derivative vanish at zero"
echo "PASS: density curvature divided by t tends to zero from the right"
echo "PASS: every positive linear lower bound fails on every full right interval"
echo "Higher-order endpoint control and global density curvature positivity remain unproved"
