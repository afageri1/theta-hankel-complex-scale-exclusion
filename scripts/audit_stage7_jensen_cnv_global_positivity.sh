#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python scripts/generate_stage7_cnv_compact_cells.py --check
lake build HodgeProofHP.Stage7ThetaJensenCNVGlobalPositivity

LOG=stage7-jensen-cnv-compact-certificates-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenCNVCompactCertificates.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_farLeadingPolynomial_mono \
  --expect HodgeProofHP.hpThetaCNV_farDerivativePolynomial_mono \
  --expect HodgeProofHP.hpThetaCNV_compact_box_positive \
  --expect HodgeProofHP.hpThetaCNV_compact_cell_certificate

for batch in 000 001 002 003 004 005; do
  LOG="stage7-jensen-cnv-compact-cells-batch${batch}-axioms.log"
  lake env lean "HodgeProofHP/Stage7ThetaJensenCNVCompactCellsBatch${batch}.lean" 2>&1 | tee "$LOG"
  python scripts/check_axioms.py "$LOG" \
    --expect "HodgeProofHP.hpThetaCNV_compact_cellsBatch${batch}"
done

LOG=stage7-jensen-cnv-global-positivity-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenCNVGlobalPositivity.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_farComparisonNumerator_pos_on_compact \
  --expect HodgeProofHP.hpThetaPhiCNVTailPositive_certified \
  --expect HodgeProofHP.hpThetaCNV_weightedTail_comparison_on_far

echo "PASS: 59 rational cells cover [1/50, 1]; all cell gaps are strictly positive"
echo "PASS: 13 complete axiom reports across the interval criterion, six batches and global theorem"
echo "PASS: actual CNV tail expression positive for every t > 0"
echo "A CNV-to-Turan bridge and unbounded good Jensen degrees are not proved by this audit"
