#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-kernel-zero-sharp-lower-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelZeroSharpLower
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelZeroSharpLower.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_exp_small_upper_sharp \
  --expect HodgeProofHP.hpThetaCNV_exp_neg_pi_lower_sharp \
  --expect HodgeProofHP.hpThetaPhi_zero_gt_eightyNine_fiftieths \
  --expect HodgeProofHP.hpThetaPhi_zero_sq_gt_certified_sharp
echo "PASS: kernel value at zero greater than 1.78 and square greater than 3.1684; weighted tail upper certificate remains unproved"
