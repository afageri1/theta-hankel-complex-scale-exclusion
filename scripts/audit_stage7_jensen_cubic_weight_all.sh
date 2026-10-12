#!/usr/bin/env bash
# Build one batch at a time; keep all per-batch axiom reports.
set -euo pipefail
cd "$(dirname "$0")/.."
generated=$(mktemp)
trap 'rm -f "$generated"' EXIT
for ((b=0; b<80; b++)); do
  printf -v batch '%03d' "$b"
  source="HodgeProofHP/Stage7ThetaJensenCubicWeightBatch${batch}.lean"
  module="HodgeProofHP.Stage7ThetaJensenCubicWeightBatch${batch}"
  LOG="stage7-jensen-cubic-weight-batch${batch}-axioms.log"
  test -f "$source" || { echo "Missing batch: $source" >&2; exit 1; }
  python scripts/generate_stage7_cubic_weight_batch.py --batch "$b" --output "$generated"
  cmp "$generated" "$source"
  echo "Building weight batch $batch ($((b+1))/80)"
  lake build "$module"
  lake env lean "$source" 2>&1 | tee "$LOG"
  python scripts/check_axioms.py "$LOG" \
    --expect "HodgeProofHP.hpThetaJensenCubicWeightBatch${batch}Neg90_bounds" \
    --expect "HodgeProofHP.hpThetaJensenCubicWeightBatch${batch}Neg55_bounds" \
    --expect "HodgeProofHP.hpThetaJensenCubicWeightBatch${batch}Neg42_bounds" \
    --expect "HodgeProofHP.hpThetaJensenCubicWeightBatch${batch}Neg15_bounds"
done
lake build HodgeProofHP.Stage7ThetaJensenCubicWeightAllBatches
echo "PASS: all 80 weight batches; 320 complete axiom reports; all dependencies allowed"
