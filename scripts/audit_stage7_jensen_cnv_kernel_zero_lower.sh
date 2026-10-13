#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-kernel-zero-lower-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelZeroLower
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelZeroLower.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_exp_small_upper \
  --expect HodgeProofHP.hpThetaCNV_exp_neg_pi_lower \
  --expect HodgeProofHP.hpThetaPhi_zero_gt_seventeen_tenths \
  --expect HodgeProofHP.hpThetaPhi_zero_sq_gt_twoHundredEightyNine_hundredths
echo "PASS: rational lower bounds for kernel value and square at zero; full endpoint derivative positivity remains unproved"
