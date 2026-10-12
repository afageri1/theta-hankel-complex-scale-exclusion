#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-weight-batch000-axioms.log
generated=$(mktemp)
trap 'rm -f "$generated"' EXIT
python scripts/generate_stage7_cubic_weight_batch.py --batch 0 --output "$generated"
cmp "$generated" HodgeProofHP/Stage7ThetaJensenCubicWeightBatch000.lean
lake build HodgeProofHP.Stage7ThetaJensenCubicWeightBatch000
lake env lean HodgeProofHP/Stage7ThetaJensenCubicWeightBatch000.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenCubicWeightBatch000Neg90_bounds \
  --expect HodgeProofHP.hpThetaJensenCubicWeightBatch000Neg55_bounds \
  --expect HodgeProofHP.hpThetaJensenCubicWeightBatch000Neg42_bounds \
  --expect HodgeProofHP.hpThetaJensenCubicWeightBatch000Neg15_bounds
