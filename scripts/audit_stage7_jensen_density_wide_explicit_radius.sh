#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
lake build HodgeProofHP.Stage7ThetaJensenDensityWideExplicitRadius

LOG=stage7-jensen-density-wide-fourth-bounds-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityWideFourthBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaDensityWideInterval_exp_two_upper \
  --expect HodgeProofHP.hpThetaDensityWideInterval_exp_half_upper \
  --expect HodgeProofHP.hpThetaDensityWideInterval_fourth_first_le \
  --expect HodgeProofHP.hpThetaDensityWideInterval_fourth_second_le \
  --expect HodgeProofHP.hpThetaDensityWideInterval_fourth_remainder_le \
  --expect HodgeProofHP.hpThetaPhi_fourthDeriv_le_1800_on_wide_density_interval

LOG=stage7-jensen-density-wide-explicit-radius-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityWideExplicitRadius.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_le_1800_mul_on_wide_density_interval \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_le_neg3319_hundredths_on_wide_density_interval \
  --expect HodgeProofHP.hpThetaPhi_deriv_le_neg3319_hundredths_mul_on_wide_density_interval \
  --expect HodgeProofHP.hpThetaPhi_deriv_div_le_neg3319_hundredths_on_wide_density_interval \
  --expect HodgeProofHP.hpThetaPhi_le_nine_fifths_on_wide_density_interval \
  --expect HodgeProofHP.hpThetaPhiDensityCurvatureFirstDerivative_ge_sixty_mul_sq \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_ge_twenty_mul_cube_on_wide_explicit_interval \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_on_wide_explicit_interval

echo "PASS: 14 complete axiom reports across wide fourth bounds and explicit radius"
echo "PASS: actual fourth kernel derivative at most 1800 on [0, 1/100]"
echo "PASS: actual density curvature derivative at least 60*t^2 on [0, 1/100]"
echo "PASS: actual density curvature at least 20*t^3 on [0, 1/100]"
echo "PASS: actual density curvature positive on (0, 1/100]"
echo "The gap (1/100, 3/20) and the remaining outer interval are not covered"
echo "Global density log concavity and all-shift cubic hyperbolicity remain unproved"
