#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-tail-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicTailBounds
lake env lean HodgeProofHP/Stage7ThetaJensenCubicTailBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenCubicWeight_abs_le_sixth \
  --expect HodgeProofHP.hpThetaJensenCubic_tail_abs_le
LOG=stage7-jensen-cubic-signs-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicEvaluationSigns
lake env lean HodgeProofHP/Stage7ThetaJensenCubicEvaluationSigns.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_neg90_neg \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_neg55_pos \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_neg42_neg \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_neg15_pos
echo "PASS: cubic absolute tail and four evaluation signs; all dependencies allowed"
