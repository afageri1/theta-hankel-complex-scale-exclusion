#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
lake build HodgeProofHP.Stage7ThetaJensenDensityBridgeExplicitRadius

LOG=stage7-jensen-density-bridge-fourth-bounds-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityBridgeFourthBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaDensityBridgeInterval_exp_two_upper \
  --expect HodgeProofHP.hpThetaDensityBridgeInterval_exp_half_upper \
  --expect HodgeProofHP.hpThetaDensityBridgeInterval_fourth_first_le \
  --expect HodgeProofHP.hpThetaDensityBridgeInterval_fourth_second_le \
  --expect HodgeProofHP.hpThetaDensityBridgeInterval_fourth_remainder_le \
  --expect HodgeProofHP.hpThetaPhi_fourthDeriv_le_1800_on_bridge_density_interval

LOG=stage7-jensen-density-bridge-explicit-radius-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityBridgeExplicitRadius.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_le_1800_mul_on_bridge_density_interval \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_le_neg3301_hundredths_on_bridge_density_interval \
  --expect HodgeProofHP.hpThetaPhi_deriv_le_neg3301_hundredths_mul_on_bridge_density_interval \
  --expect HodgeProofHP.hpThetaPhi_deriv_div_le_neg3301_hundredths_on_bridge_density_interval \
  --expect HodgeProofHP.hpThetaPhi_le_nine_fifths_on_bridge_density_interval \
  --expect HodgeProofHP.hpThetaPhiDensityCurvatureFirstDerivative_ge_twentySeven_mul_sq \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_ge_nine_mul_cube_on_bridge_explicit_interval \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_on_bridge_explicit_interval

echo "PASS: 14 complete axiom reports across bridge fourth bounds and explicit radius"
echo "PASS: actual fourth kernel derivative at most 1800 on [0, 1/50]"
echo "PASS: actual second kernel derivative at most -33.01 on [0, 1/50]"
echo "PASS: actual density curvature derivative at least 27*t^2 on [0, 1/50]"
echo "PASS: actual density curvature at least 9*t^3 on [0, 1/50]"
echo "PASS: actual density curvature positive on (0, 1/50]"
echo "The gap (1/50, 3/20) and the remaining outer interval are not covered"
echo "Global density log concavity and all-shift cubic hyperbolicity remain unproved"
