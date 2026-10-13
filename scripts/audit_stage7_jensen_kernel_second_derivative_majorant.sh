#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-kernel-second-derivative-majorant-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenKernelSecondDerivativeMajorant
lake env lean HodgeProofHP/Stage7ThetaJensenKernelSecondDerivativeMajorant.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeMajorant_nonneg \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeFactor_norm_le \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeTerm_bound_on_Ioo \
  --expect HodgeProofHP.hpTheta_quartic_factor_gaussian_bound \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeMajorant_le_gaussian \
  --expect HodgeProofHP.hpThetaGaussianKernelSecondDerivativeMajorant_summable \
  --expect HodgeProofHP.hpThetaPhi_deriv_hasDerivAt_kernelSeries \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_eq_kernelSeries
echo "PASS: summable second kernel derivative majorant and actual second kernel derivative; CNV positivity remains unproved"
