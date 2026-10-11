#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-assumption-frontier-axioms.log
bash scripts/prepare_stage5_jensen_batches.sh
lake build HodgeProofHP.Stage7ThetaJensenAssumptionFrontier
lake env lean HodgeProofHP/Stage7ThetaJensenAssumptionFrontier.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_degreeZero_realZeros \
  --expect HodgeProofHP.hpThetaJensen_degreeOne_realZeros \
  --expect HodgeProofHP.hpThetaJensen_degreeTwo_realZeros \
  --expect HodgeProofHP.hpThetaJensen_degree_le_two_realZeros \
  --expect HodgeProofHP.hpThetaJensen_allDegreesRealZeros_iff_higherDegrees \
  --expect HodgeProofHP.hpThetaJensen_RH_of_higherDegreesRealZeros
