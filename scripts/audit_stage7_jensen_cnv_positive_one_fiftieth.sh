#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Recheck the upper-bound interface before accepting the combined certificate.
bash scripts/audit_stage7_jensen_cnv_kernel_upper_one_fiftieth.sh
LOG=stage7-jensen-cnv-positive-one-fiftieth-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVPositiveOnOneFiftieth
lake env lean HodgeProofHP/Stage7ThetaJensenCNVPositiveOnOneFiftieth.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_tail_mul_secondDeriv_ge_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaCNV_mixed_term_ge_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhiCNVTailFirstDerivative_gt_certified_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_deriv_gt_certified_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_linear_lower_on_oneFiftieth \
  --expect HodgeProofHP.hpThetaPhiCNVTailExpression_pos_on_oneFiftieth
echo "PASS: actual CNV expression at least 0.045756*t and strictly positive on (0, 1/50]"
echo "CNV positivity beyond 1/50, general Turan and RH remain unproved"
