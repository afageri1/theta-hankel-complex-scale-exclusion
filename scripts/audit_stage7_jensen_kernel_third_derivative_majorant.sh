#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-kernel-third-derivative-majorant-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenKernelThirdDerivativeMajorant
lake env lean HodgeProofHP/Stage7ThetaJensenKernelThirdDerivativeMajorant.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeMajorant_nonneg \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeFactor_norm_le \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeTerm_bound_on_Ioo \
  --expect HodgeProofHP.hpTheta_quintic_factor_gaussian_bound \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeMajorant_le_gaussian \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeMajorant_summable \
  --expect HodgeProofHP.hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_eq_kernelSeries
echo "PASS: summable third kernel derivative majorant and actual third kernel derivative; CNV positivity remains unproved"
