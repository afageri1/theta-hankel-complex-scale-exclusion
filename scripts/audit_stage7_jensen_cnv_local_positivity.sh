#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-local-positivity-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVLocalPositivity
lake env lean HodgeProofHP/Stage7ThetaJensenCNVLocalPositivity.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_div_tendsto_right \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_eventually_linear_lower \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_exists_linear_lower_interval \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_exists_positive_interval
echo "PASS: actual CNV expression positive on some right interval; explicit radius and global positivity remain unproved"
