#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-kernel-far-decreasing-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelFarDecreasing
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelFarDecreasing.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_far_parameter_ge_thirteen_fourths \
  --expect HodgeProofHP.hpThetaCNV_firstDerivativeFactor_neg \
  --expect HodgeProofHP.hpThetaCNV_kernelDerivativeTerm_neg_on_far \
  --expect HodgeProofHP.hpThetaPhi_deriv_neg_on_far \
  --expect HodgeProofHP.hpThetaPhi_strictAntiOn_far \
  --expect HodgeProofHP.hpThetaPhi_le_two_on_nonnegative
echo "PASS: actual kernel strictly decreasing on [1/50, infinity) and at most 2 for t >= 0"
echo "Quantitative far-field weighted-tail comparison and global CNV positivity remain unproved"
