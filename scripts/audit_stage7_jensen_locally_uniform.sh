#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-locally-uniform-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenLocallyUniformConvergence
lake env lean HodgeProofHP/Stage7ThetaJensenLocallyUniformConvergence.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_compact \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_tendstoLocallyUniformly \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_tendsto \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_differentiable \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_deriv_tendstoLocallyUniformly \
  --expect HodgeProofHP.hpThetaJensenGeneratingFunction_zero_ne_zero \
  --expect HodgeProofHP.hpThetaJensenGeneratingFunction_not_identically_zero
