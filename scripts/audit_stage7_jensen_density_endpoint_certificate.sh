#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-endpoint-certificate-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityEndpointCertificate
lake env lean HodgeProofHP/Stage7ThetaJensenDensityEndpointCertificate.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_zero_le_nine_fifths \
  --expect HodgeProofHP.hpThetaDensityEndpoint_monomial_geometric \
  --expect HodgeProofHP.hpThetaDensityEndpoint_second_first_le \
  --expect HodgeProofHP.hpThetaDensityEndpoint_fourth_first_le \
  --expect HodgeProofHP.hpThetaDensityEndpoint_fourth_second_le \
  --expect HodgeProofHP.hpThetaDensityEndpoint_second_remainder_le \
  --expect HodgeProofHP.hpThetaDensityEndpoint_fourth_remainder_le \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_zero_le_neg32 \
  --expect HodgeProofHP.hpThetaPhi_fourthDeriv_zero_le_1700 \
  --expect HodgeProofHP.hpThetaPhiDensityEndpointCoefficient_ge_twelve \
  --expect HodgeProofHP.hpThetaPhiDensityEndpointCoefficient_pos \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_exists_cubic_lower_certified \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_exists_positive_interval
echo "PASS: 13 complete axiom reports; all dependencies allowed"
echo "PASS: Phi(0) <= 1.8, Phi second derivative at zero <= -32, fourth derivative <= 1700"
echo "PASS: actual density endpoint coefficient at least 12 and strictly positive"
echo "PASS: actual density curvature has an existential lower bound 2*t^3 near zero"
echo "An explicit radius and global density curvature positivity remain unproved"
