#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python scripts/generate_stage7_cnv_second_interval_cells.py --check
LOG=stage7-jensen-cnv-interval-gluing-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVIntervalGluing
lake env lean HodgeProofHP/Stage7ThetaJensenCNVIntervalGluing.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_interval_lower_glue
for b in $(seq 0 19); do
  printf -v batch '%03d' "$b"
  module="Stage7ThetaJensenCNVSecondCellsBatch${batch}"
  LOG="stage7-jensen-cnv-second-cells-batch${batch}-axioms.log"
  lake build "HodgeProofHP.${module}"
  lake env lean "HodgeProofHP/${module}.lean" 2>&1 | tee "$LOG"
  python scripts/check_axioms.py "$LOG" \
    --expect "HodgeProofHP.hpThetaCNV_secondDerivative_cellsBatch${batch}"
done
LOG=stage7-jensen-cnv-second-on-one-fiftieth-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelSecondOnOneFiftieth
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelSecondOnOneFiftieth.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_secondDerivative_firstTerm_ge_neg35_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_ge_neg35_on_oneFiftieth
echo "PASS: 200 cells cover [0, 1/50]; actual second kernel derivative at least -35"
echo "PASS: 23 complete axiom reports across gluing, 20 batches and final bounds"
echo "CNV positivity on the full interval and global CNV positivity remain unproved"
