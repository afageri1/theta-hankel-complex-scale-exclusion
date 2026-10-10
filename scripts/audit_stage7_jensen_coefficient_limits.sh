#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-coefficient-limit-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCoefficientLimits
lake env lean HodgeProofHP/Stage7ThetaJensenCoefficientLimits.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_succ \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_factor_tendsto \
  --expect HodgeProofHP.hpThetaJensenRescalingWeight_tendsto
