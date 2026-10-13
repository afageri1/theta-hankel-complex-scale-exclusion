#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-kernel-second-derivative-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenKernelSecondDerivativeCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenKernelSecondDerivativeCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeTerm_hasDerivAt \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeTerm_deriv \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeTerm_norm_summable \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeTerm_summable \
  --expect HodgeProofHP.hpThetaPhi_deriv_hasDerivAt_of_second_local_majorant \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_eq_tsum_of_local_majorant
echo "PASS: second kernel derivative criterion; second majorant and CNV positivity remain unproved"
