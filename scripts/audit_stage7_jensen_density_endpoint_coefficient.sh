#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-endpoint-coefficient-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityEndpointCoefficient
lake env lean HodgeProofHP/Stage7ThetaJensenDensityEndpointCoefficient.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_density_first_reflection \
  --expect HodgeProofHP.hpThetaPhi_density_second_reflection \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_zero \
  --expect HodgeProofHP.hpThetaPhi_deriv_div_tendsto_right \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_div_tendsto_right \
  --expect HodgeProofHP.hpThetaPhiDensityCurvatureFirstDerivative_div_sq \
  --expect HodgeProofHP.hpThetaPhiDensityCurvatureFirstDerivative_div_sq_tendsto_right \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_exists_cubic_lower_of_coefficient_pos
echo "PASS: kernel derivative reflection and actual third derivative at zero"
echo "PASS: actual density curvature derivative divided by t squared tends to its endpoint coefficient"
echo "PASS: a positive endpoint coefficient implies an existential cubic lower bound"
echo "A numerical sign certificate, explicit radius and global density curvature positivity remain unproved"
