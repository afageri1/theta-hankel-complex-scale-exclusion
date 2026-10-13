#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-kernel-third-derivative-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenKernelThirdDerivativeCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenKernelThirdDerivativeCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeTerm_hasDerivAt \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeTerm_deriv \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeTerm_norm_summable \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeTerm_summable \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_hasDerivAt_of_third_local_majorant \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_eq_tsum_of_local_majorant
echo "PASS: third kernel derivative criterion; third majorant and CNV positivity remain unproved"
