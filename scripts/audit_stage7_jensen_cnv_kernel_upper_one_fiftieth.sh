#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-kernel-upper-one-fiftieth-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelUpperOnOneFiftieth
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelUpperOnOneFiftieth.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_endpointUpper_le_two_of_bounds \
  --expect HodgeProofHP.hpThetaCNV_exp_oneFiftieth_upper \
  --expect HodgeProofHP.hpThetaCNV_exp_oneTwentyFifth_upper \
  --expect HodgeProofHP.hpThetaCNV_exp_neg_firstHalf_upper \
  --expect HodgeProofHP.hpThetaCNV_exp_neg_secondHalf_upper \
  --expect HodgeProofHP.hpThetaCNV_endpointUpper_firstHalf_le_two \
  --expect HodgeProofHP.hpThetaCNV_endpointUpper_secondHalf_le_two \
  --expect HodgeProofHP.hpThetaPhi_le_two_on_oneFiftieth
echo "PASS: actual kernel at most 2 on [0, 1/50], including the whole Gaussian series"
echo "CNV derivative lower bound and positivity on the full interval remain unproved"
