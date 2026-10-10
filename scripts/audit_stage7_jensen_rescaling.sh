#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-rescaling-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenRescalingBounds
lake env lean HodgeProofHP/Stage7ThetaJensenRescalingBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_nonneg \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_zero \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_one \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_eq_zero_of_lt \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_le_factorial \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_abs_le_factorial
