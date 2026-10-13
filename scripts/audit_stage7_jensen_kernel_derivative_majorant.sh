#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-kernel-derivative-majorant-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenKernelDerivativeMajorant
lake env lean HodgeProofHP/Stage7ThetaJensenKernelDerivativeMajorant.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeMajorant_nonneg \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeFactor_norm_le \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeTerm_bound_on_Ioo \
  --expect HodgeProofHP.hpTheta_cubic_factor_gaussian_bound \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeMajorant_le_gaussian \
  --expect HodgeProofHP.hpThetaGaussianKernelDerivativeMajorant_summable \
  --expect HodgeProofHP.hpThetaPhi_hasDerivAt_kernelSeries \
  --expect HodgeProofHP.hpThetaPhi_deriv_eq_kernelSeries
echo "PASS: summable kernel derivative majorant and actual kernel derivative; CNV positivity remains unproved"
