#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-curvature-pilot-cell-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityCurvaturePilotCell
lake env lean HodgeProofHP/Stage7ThetaJensenDensityCurvaturePilotCell.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaDensityPilot_exp_lower \
  --expect HodgeProofHP.hpThetaDensityPilot_exp_upper \
  --expect HodgeProofHP.hpThetaDensityPilot_exp_fourteen_lower \
  --expect HodgeProofHP.hpThetaDensityPilot_parameter_bounds \
  --expect HodgeProofHP.hpThetaDensityPilot_secondTerm_le_geometric \
  --expect HodgeProofHP.hpThetaDensityPilot_second_remainder_le \
  --expect HodgeProofHP.hpThetaDensityPilot_scaled_kernel_bounds \
  --expect HodgeProofHP.hpThetaDensityPilot_scaled_neg_deriv_bounds \
  --expect HodgeProofHP.hpThetaDensityPilot_scaled_second_deriv_le \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_ge_seventy_gaussian_sq_on_pilot \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_on_pilot_cell
echo "PASS: 11 complete axiom reports; all dependencies allowed"
echo "PASS: entire second derivative remainder bounded by twice the first Gaussian profile"
echo "PASS: actual scaled kernel, negative first derivative and second derivative certified on the pilot cell"
echo "PASS: actual density curvature at least 70 times the squared first Gaussian profile"
echo "PASS: actual density curvature positive for 1/5 <= t <= 200001/1000000"
echo "The pilot cell does not connect to the endpoint interval; complementary coverage remains unproved"
echo "Global density log concavity, all-shift cubic hyperbolicity and unbounded degrees remain unproved"
