#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash scripts/prepare_stage5_jensen_batches.sh
generated=$(mktemp -d)
trap 'rm -rf "$generated"' EXIT
python scripts/generate_stage7_cubic_rectangles.py --output-dir "$generated"
for p in 90 55 42 15; do
  module="Stage7ThetaJensenCubicRectanglesNeg${p}"
  cmp "$generated/${module}.lean" "HodgeProofHP/${module}.lean"
  LOG="stage7-jensen-cubic-rectangles-neg${p}-axioms.log"
  lake build "HodgeProofHP.${module}"
  lake env lean "HodgeProofHP/${module}.lean" 2>&1 | tee "$LOG"
  python scripts/check_axioms.py "$LOG" \
    --expect "HodgeProofHP.hpThetaJensenCubicNeg${p}_rectangleBatch_bounds" \
    --expect "HodgeProofHP.hpThetaJensenCubicNeg${p}_rectangle_lower_numeric" \
    --expect "HodgeProofHP.hpThetaJensenCubicNeg${p}_rectangle_upper_numeric"
done
echo "PASS: all four signed rectangle totals; all dependencies allowed"
