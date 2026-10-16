#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-outer-positivity-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVOuterPositivity
lake env lean HodgeProofHP/Stage7ThetaJensenCNVOuterPositivity.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_exp_three_mul_ge_linear \
  --expect HodgeProofHP.hpThetaCNV_farParameter_ge_eight \
  --expect HodgeProofHP.hpThetaCNV_farKernelRatio_mul_parameter_le \
  --expect HodgeProofHP.hpThetaCNV_scalar_numerator_pos \
  --expect HodgeProofHP.hpThetaCNV_farComparisonNumerator_pos_on_outer \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_pos_on_outer \
  --expect HodgeProofHP.hpThetaCNV_weightedTail_comparison_on_outer \
  --expect HodgeProofHP.hpThetaPhiCNVTailPositive_of_compact_numerator
echo "PASS: actual weighted-tail comparison and CNV positivity for every t >= 1"
echo "CNV positivity on the compact interval [1/50, 1] remains unproved"
