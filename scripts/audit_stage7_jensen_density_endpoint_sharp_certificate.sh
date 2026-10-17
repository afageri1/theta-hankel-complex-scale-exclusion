#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-endpoint-sharp-certificate-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityEndpointSharpCertificate
lake env lean HodgeProofHP/Stage7ThetaJensenDensityEndpointSharpCertificate.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaDensitySharp_second_gaussian_le \
  --expect HodgeProofHP.hpThetaDensitySharp_second_remainder_le \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_zero_le_neg3337_hundredths \
  --expect HodgeProofHP.hpThetaPhiDensityEndpointCoefficient_ge_twoHundredEighty \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_exists_stronger_cubic_lower
echo "PASS: 5 complete axiom reports; all dependencies allowed"
echo "PASS: second Gaussian term at zero at most 1.43 and full remaining tail at most 0.001"
echo "PASS: actual second kernel derivative at zero at most -33.37"
echo "PASS: actual density endpoint coefficient at least 280"
echo "PASS: existential local lower bound 46*t^3"
echo "No larger explicit endpoint radius or new interval coverage is established here"
echo "Global density log concavity and all-shift cubic hyperbolicity remain unproved"
