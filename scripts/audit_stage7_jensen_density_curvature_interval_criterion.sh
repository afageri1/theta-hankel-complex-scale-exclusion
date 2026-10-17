#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-curvature-interval-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityCurvatureIntervalCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenDensityCurvatureIntervalCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaDensityCurvatureBoxMargin_le \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_div_scale_sq \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_lower_of_scaled_bounds \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_of_scaled_bounds \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_interval_pos_of_scaled_bounds \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_secondDeriv_neg_on_explicit_interval \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_strictConcaveOn_explicit_interval \
  --expect HodgeProofHP.hpThetaPhiDensityNormalizedSlope_strictAntiOn_explicit_interval \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_of_compact_and_outer \
  --expect HodgeProofHP.hpThetaPhiSquareDensity_log_strictConcaveOn_of_compact_and_outer
echo "PASS: 10 complete axiom reports; all dependencies allowed"
echo "PASS: scaled density curvature interval criterion retains signed second derivative bounds"
echo "PASS: actual log density strictly concave for 0 < x < 1/100000000"
echo "PASS: actual normalized density slope strictly decreasing on (0, 1/10000]"
echo "PASS: conditional gluing of endpoint, compact and outer density curvature certificates"
echo "Complementary numerical coverage and global density curvature positivity remain unproved"
echo "All-shift cubic hyperbolicity and unbounded good Jensen degrees remain unproved"
