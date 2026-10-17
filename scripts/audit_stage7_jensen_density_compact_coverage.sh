#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python scripts/generate_stage7_density_curvature_cells.py --check
lake build HodgeProofHP.Stage7ThetaJensenDensityCompactCoverage

COMMON_LOG=stage7-jensen-density-rational-cells-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityCurvatureRationalCells.lean 2>&1 | tee "$COMMON_LOG"
python scripts/check_axioms.py "$COMMON_LOG" \
  --expect HodgeProofHP.hpThetaDensityCells_parameter_bounds \
  --expect HodgeProofHP.hpThetaDensityCells_ratio_bound \
  --expect HodgeProofHP.hpThetaDensityCells_interval_certificate \
  --expect HodgeProofHP.hpThetaDensityCells_positive_glue

for batch in 000 001 002 003 004 005 006 007; do
  LOG="stage7-jensen-density-compact-batch${batch}-axioms.log"
  lake env lean "HodgeProofHP/Stage7ThetaJensenDensityCompactCellsBatch${batch}.lean" 2>&1 | tee "$LOG"
  python scripts/check_axioms.py "$LOG" \
    --expect "HodgeProofHP.hpThetaDensityCompact_cellsBatch${batch}"
done

FINAL_LOG=stage7-jensen-density-compact-coverage-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenDensityCompactCoverage.lean 2>&1 | tee "$FINAL_LOG"
python scripts/check_axioms.py "$FINAL_LOG" \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_on_threeTwentieths_oneFifth \
  --expect HodgeProofHP.hpThetaPhiDensityCurvature_pos_on_compact_extension

echo "PASS: 14 complete axiom reports across cell criterion, eight batches and final coverage"
echo "PASS: 155 adjacent rational cells cover [3/20, 1/5] with positive margins"
echo "PASS: actual density curvature positive on [3/20, 200001/1000000]"
echo "The gap (1/10000, 3/20) and the remaining outer interval are not covered"
echo "Global density log concavity and all-shift cubic hyperbolicity remain unproved"
