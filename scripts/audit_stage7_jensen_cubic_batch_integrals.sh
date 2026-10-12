#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-partition-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicIntegralPartition
lake env lean HodgeProofHP/Stage7ThetaJensenCubicIntegralPartition.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenCubic_uniformCellIntegral_sum \
  --expect HodgeProofHP.hpThetaJensenCubic_batchIntegral_of_bounds
bash scripts/prepare_stage5_jensen_batches.sh
for ((b=0; b<80; b++)); do
  printf -v batch '%03d' "$b"
  lake build "HodgeProofHP.Stage7ThetaJensenCubicWeightBatch${batch}"
done
generated=$(mktemp)
trap 'rm -f "$generated"' EXIT
for point in 90 55 42 15; do
  module="HodgeProofHP.Stage7ThetaJensenCubicBatchIntegralsNeg${point}"
  source="HodgeProofHP/Stage7ThetaJensenCubicBatchIntegralsNeg${point}.lean"
  LOG="stage7-jensen-cubic-batch-integrals-neg${point}-axioms.log"
  python scripts/generate_stage7_cubic_batch_integrals.py --point "$point" --output "$generated"
  cmp "$generated" "$source"
  lake build "$module"
  lake env lean "$source" 2>&1 | tee "$LOG"
  args=()
  for ((b=0; b<80; b++)); do
    printf -v batch '%03d' "$b"
    args+=(--expect "HodgeProofHP.hpThetaJensenCubicBatch${batch}Neg${point}_integral_bounds")
  done
  python scripts/check_axioms.py "$LOG" "${args[@]}"
done
echo "PASS: signed partition and all 320 batch integral bounds; all dependencies allowed"
