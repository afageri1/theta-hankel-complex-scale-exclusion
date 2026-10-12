#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-assumption-frontier-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicAssumptionFrontier
lake env lean HodgeProofHP/Stage7ThetaJensenCubicAssumptionFrontier.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_degreeThree_realZeros \
  --expect HodgeProofHP.hpThetaJensen_degree_le_three_realZeros \
  --expect HodgeProofHP.hpThetaJensen_allDegreesRealZeros_iff_degreesFromFour \
  --expect HodgeProofHP.hpThetaJensen_RH_of_degreesFromFourRealZeros
echo "PASS: degrees zero through three; higher-degree RH hypothesis remains explicit"
