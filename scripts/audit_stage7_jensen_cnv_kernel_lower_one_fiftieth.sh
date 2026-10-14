#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-kernel-lower-one-fiftieth-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVKernelLowerOnOneFiftieth
lake env lean HodgeProofHP/Stage7ThetaJensenCNVKernelLowerOnOneFiftieth.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_deriv_ge_neg35_mul_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhi_deriv_ge_neg_seven_tenths_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhi_ge_zero_sub_seven_tenths_mul_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhi_gt_eightHundredEightyThree_fiveHundredths_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhi_sq_gt_certified_on_oneFiftieth
echo "PASS: actual first kernel derivative at least -0.7 and kernel greater than 1.766 on [0, 1/50]"
echo "Kernel upper bound and CNV positivity on the full interval remain unproved"
