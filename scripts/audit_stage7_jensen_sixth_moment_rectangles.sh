#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-sixth-moment-rectangles-axioms.log
bash scripts/prepare_stage5_jensen_batches.sh
generated=$(mktemp)
trap 'rm -f "$generated"' EXIT
python scripts/generate_stage7_sixth_rectangles.py --output "$generated"
cmp "$generated" HodgeProofHP/Stage7ThetaJensenSixthMomentRectangles.lean
lake build HodgeProofHP.Stage7ThetaJensenSixthMomentRectangles
lake env lean HodgeProofHP/Stage7ThetaJensenSixthMomentRectangles.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_sixthRectangleBatch_bounds \
  --expect HodgeProofHP.hpThetaJensen_sixthRectangle_lower_numeric \
  --expect HodgeProofHP.hpThetaJensen_sixthRectangle_upper_numeric
