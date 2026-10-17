#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build HodgeProofHP.Stage7ThetaJensenKernelFourthDerivativeMajorant
lake env lean HodgeProofHP/Stage7ThetaJensenKernelFourthDerivativeCriterion.lean 2>&1 | tee "stage7-jensen-kernel-fourth-derivative-criterion-axioms.log"
python scripts/check_axioms.py "stage7-jensen-kernel-fourth-derivative-criterion-axioms.log" \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeTerm_hasDerivAt \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeTerm_deriv \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeTerm_norm_summable \
  --expect HodgeProofHP.hpThetaGaussianKernelThirdDerivativeTerm_summable \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_hasDerivAt_of_fourth_local_majorant \
  --expect HodgeProofHP.hpThetaPhi_fourthDeriv_eq_tsum_of_local_majorant
lake env lean HodgeProofHP/Stage7ThetaJensenKernelFourthDerivativeMajorant.lean 2>&1 | tee "stage7-jensen-kernel-fourth-derivative-majorant-axioms.log"
python scripts/check_axioms.py "stage7-jensen-kernel-fourth-derivative-majorant-axioms.log" \
  --expect HodgeProofHP.hpThetaGaussianKernelFourthDerivativeMajorant_nonneg \
  --expect HodgeProofHP.hpThetaGaussianKernelFourthDerivativeFactor_norm_le \
  --expect HodgeProofHP.hpThetaGaussianKernelFourthDerivativeTerm_bound_on_Ioo \
  --expect HodgeProofHP.hpTheta_sextic_factor_gaussian_bound \
  --expect HodgeProofHP.hpThetaGaussianKernelFourthDerivativeMajorant_le_gaussian \
  --expect HodgeProofHP.hpThetaGaussianKernelFourthDerivativeMajorant_summable \
  --expect HodgeProofHP.hpThetaPhi_thirdDeriv_hasDerivAt_kernelSeries \
  --expect HodgeProofHP.hpThetaPhi_fourthDeriv_eq_kernelSeries
echo "PASS: fourth Gaussian derivative terms and a summable local sextic majorant"
echo "PASS: actual fourth theta kernel derivative equals its explicit Gaussian series"
echo "PASS: 14 complete axiom reports across the criterion and majorant"
echo "Fourth derivative numerical bounds and positive higher-order density endpoint control remain unproved"
