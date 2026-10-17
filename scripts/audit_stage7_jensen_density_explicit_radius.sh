#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build HodgeProofHP.Stage7ThetaJensenDensityExplicitRadius

LOG=stage7-jensen-density-fourth-near-zero-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityFourthNearZero.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaDensityInterval_exp_two_upper \
  --expect HodgeProofHP.hpThetaDensityInterval_exp_half_upper \
  --expect HodgeProofHP.hpThetaDensityInterval_fourth_first_le \
  --expect HodgeProofHP.hpThetaDensityInterval_fourth_second_le \
  --expect HodgeProofHP.hpThetaDensityInterval_fourth_remainder_le \
  --expect HodgeProofHP.hpThetaPhi_fourthDeriv_le_1700_on_density_interval

LOG=stage7-jensen-density-explicit-radius-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityExplicitRadius.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_le_1700_mul_on_density_interval \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_le_neg3199_hundredths_on_density_interval \
  --expect HodgeProofHP.hpThetaPhi_deriv_le_neg3199_hundredths_mul_on_density_interval \
  --expect HodgeProofHP.hpThetaPhi_deriv_div_le_neg3199_hundredths_on_density_interval \
  --expect HodgeProofHP.hpThetaPhi_le_nine_fifths_on_density_interval \
  --expect HodgeProofHP.hpThetaPhiDensityCurvatureFirstDerivative_ge_nine_mul_sq \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_ge_three_mul_cube_on_explicit_interval \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_on_explicit_interval

echo "PASS: 14 complete axiom reports across uniform fourth bounds and explicit density radius"
echo "PASS: actual fourth kernel derivative at most 1700 on [0, 1/10000]"
echo "PASS: actual density curvature derivative at least 9*t^2 on [0, 1/10000]"
echo "PASS: actual density curvature at least 3*t^3 on [0, 1/10000]"
echo "PASS: actual density curvature strictly positive on (0, 1/10000]"
echo "This endpoint interval does not establish global density log concavity"
echo "Higher-moment comparison, all-shift cubic hyperbolicity and unbounded degrees remain unproved"
