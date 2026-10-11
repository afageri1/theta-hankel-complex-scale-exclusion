#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-sixth-moment-cells-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenSixthMomentCellBounds
lake env lean HodgeProofHP/Stage7ThetaJensenSixthMomentCellBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_natPowerCellIntegral_bounds \
  --expect HodgeProofHP.hpThetaJensen_sixthCellIntegral_bounds \
  --expect HodgeProofHP.hpThetaJensen_sixthCellIntegral_endpoint_bounds \
  --expect HodgeProofHP.hpThetaJensen_natPowerUniformCellIntegral_sum \
  --expect HodgeProofHP.hpThetaJensen_sixthMoment_1600CellIntegral_sum
