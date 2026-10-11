#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cofinal-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCofinalCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenCofinalCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_rescaled_ne_zero_of_degreeRealZeros \
  --expect HodgeProofHP.hpThetaJensen_nonrealZeroExclusion_of_cofinalRealZeros \
  --expect HodgeProofHP.hpThetaJensen_RH_of_cofinalRealZeros \
  --expect HodgeProofHP.hpThetaJensen_eventually_nonrealZero_of_not_RH
