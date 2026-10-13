#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-kernel-derivative-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenKernelDerivativeCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenKernelDerivativeCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaGaussianKernelTerm_hasDerivAt \
  --expect HodgeProofHP.hpThetaGaussianKernelTerm_deriv \
  --expect HodgeProofHP.hpThetaPhi_hasDerivAt_of_local_majorant \
  --expect HodgeProofHP.hpThetaPhi_deriv_eq_tsum_of_local_majorant
echo "PASS: kernel derivative criterion; local majorant and CNV positivity remain obligations"
